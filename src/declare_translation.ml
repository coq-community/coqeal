open Parametricity
open Vars
open Term
open Constr
open Libnames

let default_continuation = ignore

let add_coercions env evdr term = 
  (*
    let glob = Detyping.detype true [] env !evdr term in 
    Pretyping.understand_tcc_evars env evdr glob
  *)
  term

let print_translation_command retype arity c =  
  let (evd, env) = Lemmas.get_current_context () in 
  let (evd, c) = Constrintern.interp_open_constr env evd c in
  let evdr = ref evd in 
  try
    let c_R = translate arity evdr env c in 
    let c_R = if retype then add_coercions env evdr c_R else c_R in
    Pp.(msg_notice (Printer.pr_lconstr_env env !evdr c_R))
  with e -> 
    Pp.(msg_notice (str (Printexc.to_string e)))


(** Adds the definition name := ⟦a⟧ : ⟦b⟧ a a. *)
let declare_abstraction ?(opaque = false) ?(continuation = default_continuation) ?kind order evdr env a name =
  let program_mode_before = Flags.is_program_mode () in 
  Obligations.set_program_mode !Parametricity.program_mode;
  debug_string [`Abstraction] "### Begin declaration !";
  debug_evar_map [`Abstraction] "starting evarmap:" !evdr;
  let b = Retyping.get_type_of env !evdr a in
  debug_string [`Time] "starting translation of term";
  debug [`Abstraction] "translate term :" env !evdr a;
  let a_R = translate order evdr env a  in
  let a_R = add_coercions env evdr a_R in
  let a_R = Typing.solve_evars env evdr a_R in
  debug [`Abstraction] "translate type :" env !evdr b;
  debug_string [`Time] "starting translation of type";
  let b_R = relation order evdr env b in 
  debug_string [`Time] "done translating";
  let sub = range (fun k -> prime order k a) order in 
  let b_R = substl sub b_R in
  debug_string [`Time] "detyping ...";
  let b_R = add_coercions env evdr b_R in
  debug_string [`Time] "typing ...";
  let b_R = Typing.solve_evars env evdr b_R in
  debug_string [`Time] "retyping ...";
  let b_R' = Retyping.get_type_of env !evdr a_R in 
  debug_string [`Time] "unifying ...";
  evdr := Unification.w_unify env !evdr Reduction.CUMUL b_R' b_R; 
  debug_evar_map [`Abstraction] "after type checking (before simplification):" !evdr; 
  let nf, _ = Evarutil.e_nf_evars_and_universes evdr in 
  let a_R, b_R = nf a_R, nf b_R in 
  debug [`Abstraction] "translation of term, a_R = " env !evdr a_R;
  let evd = !evdr in
  debug_evar_map [`Abstraction] "after type checking :" evd; 
  debug [`Abstraction] "infered type is b_R' = " env evd b_R';
  debug_string [`Abstraction] "Cooking obligation ...";
  let obls, _, a_R, b_R = Obligations.eterm_obligations env name evd 0 a_R b_R in 
  let ctx = Evd.evar_universe_context evd in
  let hook = 
    match kind_of_term a with 
      | Const cte when 
          (try ignore (Relations.get_constant order (Univ.out_punivs cte)); false with Not_found -> true)
        -> 
         (Lemmas.mk_hook (fun _ dcl -> 
           Pp.(Flags.if_verbose msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name)))); 
            Relations.declare_relation order (Globnames.ConstRef (Univ.out_punivs cte)) dcl; 
            continuation ()))
      | _ -> (Lemmas.mk_hook (fun _ dcl -> continuation ()))
  in
  debug_string [`Abstraction] "add_definition:";
  debug [`Abstraction] "a_R:\t" env evd a_R;
  debug [`Abstraction] "b_R:\t" env evd b_R;
  ignore (Obligations.add_definition ~opaque name ~hook ?kind ~tactic:(snd (Relations.get_parametricity_tactic ())) ~term:a_R b_R ctx obls);
  Obligations.set_program_mode program_mode_before

let translate_command arity c names =  
  let (evd, env) = Lemmas.get_current_context () in 
  let (evd, c) = Constrintern.interp_open_constr env evd c in
  let cte_option =
    match Term.kind_of_term c with Term.Const cte -> Some cte | _ -> None 
  in 
  let poly, opaque = 
    match cte_option with
    | Some (cte, _) -> 
        let cb = Global.lookup_constant cte in 
        Declarations.(cb.const_polymorphic, match cb.const_body with Def _ -> false | _ -> true)
    | None -> false, false
  in 
  let kind = Decl_kinds.(Global, poly, Definition) in
  let name =
    match names, cte_option with
      | None, Some cte -> 
             Names.id_of_string 
          @@ translate_string arity 
          @@ Names.Label.to_string 
          @@ Names.Constant.label 
          @@ Univ.out_punivs cte
      | Some name, _ -> name
      | _ -> error (Pp.str "In the case of a constant, Abstraction expects 0 or 1 identifier. Otherwise, 1 identifier.")
  in
  declare_abstraction ~opaque ~kind arity (ref evd) env c name 


let declare_inductive ?(continuation = default_continuation) arity evd env ((mut_ind, _) as ind) = 
  let mut_body, _ = Inductive.lookup_mind_specif env ind in
  let inst, ctx = 
    let open Univ in 
    if mut_body.Declarations.mind_polymorphic then 
      Universes.fresh_instance_from mut_body.Declarations.mind_universes None 
    else
      Instance.empty, ContextSet.empty
  in
  evd := Evd.merge_context_set Evd.univ_flexible !evd ctx; 
  debug_string [`Inductive] "Translating mind body ..."; 
  let translation_entry = Parametricity.translate_mind_body arity evd env mut_ind mut_body inst in 
  debug_string [`Inductive] "Translating mind body ... done."; 
  let translation_entry = Parametricity.retype_mind_entry env evd translation_entry in
  debug_string [`Inductive] "Retyping done."; 
  let size = Declarations.(Array.length mut_body.mind_packets) in 
  let mut_ind_R = Command.declare_mutual_inductive_with_eliminations translation_entry [] in
  for k = 0 to size-1 do
    Relations.declare_inductive_relation arity (mut_ind, k) (mut_ind_R,k)
  done; 
  continuation ()

let translate_inductive_command arity c name = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, c) = Constrintern.interp_open_constr env sigma c in
  let (ind, _), _ =
    try 
      Inductive.find_rectype env c
    with Not_found -> 
      error (Pp.(str "Unable to locate an inductive in " ++ Printer.pr_constr_env env sigma c))
  in
  try
    let ind_R = Relations.get_inductive arity ind in 
    error (Pp.(str "The inductive " ++ Printer.pr_inductive env ind ++ str " already as the following registered translation " ++ Printer.pr_inductive env ind_R))
  with Not_found -> 
  let evd = ref sigma in 
  declare_inductive arity evd env ind

let declare_realizer ?(continuation = default_continuation) ?kind ?real arity evd env name var  = 
  let gref = Term.(match kind_of_term var with 
     | Var id -> Globnames.VarRef id 
     | Const (cst, _) -> Globnames.ConstRef cst
     | _ -> error (Pp.str "Realizer works only for variables and constants.")) in 
  let sigma, typ = Typing.e_type_of ~refresh:true env !evd var in
  evd := sigma;
  let typ_R = Parametricity.relation arity evd env typ in 
  let sub = range (fun _ -> var) arity in 
  let typ_R = Vars.substl sub typ_R in
  debug [`Realizer] "typ_R =" env sigma typ_R;
  (* Obligations.check_evars env !evd; *)
  let real = 
    match real with Some real ->
      let realtyp = Retyping.get_type_of env sigma real in
      debug [`Realizer] "realtyp =" env sigma realtyp;
      ignore (Evarconv.e_cumul env evd realtyp typ_R); real
    | None ->
      (let sigma, real = Evarutil.new_evar env !evd typ_R in 
      evd := sigma; real)
  in
  debug [`Realizer] "real =" env sigma real;
  let kind = Decl_kinds.Global, true, Decl_kinds.Definition in
  let name = match name with Some x -> x | _ -> 
     let name_str =  Term.(match kind_of_term var with 
     | Var id -> Names.Id.to_string id 
     | Const (cst, _) -> Names.Label.to_string (Names.Constant.label cst)
     | _ -> assert false) 
     in 
     let name_R = translate_string arity name_str in 
     Names.Id.of_string name_R
  in 
  let sigma = !evd in 
  
  debug_evar_map [`Realizer] "ear_map =" sigma;

  let obls, _, real, typ_R = Obligations.eterm_obligations env name sigma 0 real typ_R in 
  let ctx = Evd.evar_universe_context sigma in
  let hook = Lemmas.mk_hook (fun _ dcl -> 
    Pp.(msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name)))); 
    Relations.declare_relation arity gref dcl; 
    continuation ()) in
  ignore (Obligations.add_definition name ~kind ~term:real ~hook typ_R ctx obls)

  
let realizer_command arity name var real = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, var) = Constrintern.interp_open_constr env sigma var in
  Obligations.check_evars env sigma;
  let (sigma, real) = Constrintern.interp_open_constr env sigma real in
  declare_realizer arity (ref sigma) env name var ~real


let rec list_continuation final f l _ = match l with [] -> final ()
   | hd::tl -> f (list_continuation final f tl) hd

let rec translate_module_command arity r = 
  let (loc, qid) = qualid_of_reference r in 
  let globdir = Nametab.locate_dir qid in 
  match globdir with 
  | DirModule (_, (mp, _)) -> 
     let mb = try 
       Global.lookup_module mp 
     with Not_found -> error Pp.(str "Unknown Module " ++ pr_qualid qid) in 
     declare_module arity mb
  | _ -> assert false

and id_of_module_path mp = 
 let open Names in 
 let open ModPath in 
 match mp with
   | MPdot (_, lab) -> Label.to_id lab
   | MPfile dp -> List.hd (DirPath.repr dp)
   | MPbound id -> MBId.to_id id



and declare_module ?(continuation = ignore) arity mb = 
  let open Declarations in 
  let mp = mb.mod_mp in 
  match mb.mod_expr, mb.mod_type with 
  | Algebraic _, NoFunctor fields 
  | FullStruct, NoFunctor fields -> 
     let id = id_of_module_path mp in
     let id_R = translate_id arity id in 
     debug_string [`Module] (Printf.sprintf "start module: '%s' (translating '%s')." 
       (Names.Id.to_string id_R) (Names.Id.to_string id));
     let mp_R = Global.start_module id_R in
     (* I have no idea what I'm doing here : *)
     let fs = Summary.freeze_summaries ~marshallable:`No in 
     let _ = Lib.start_module None id_R mp_R fs in
     list_continuation
     (fun _ -> 
       debug_string [`Module] (Printf.sprintf "end module: '%s'." (Names.Id.to_string id_R));
       ignore (Declaremods.end_module ()); continuation ())
     (fun continuation -> function
     | (lab, SFBconst cb) when (match cb.const_body with OpaqueDef _ -> false | Undef _ -> true | _ -> false) ->
       let (evd, env) = ref Evd.empty, Global.env () in 
       let cst = Mod_subst.constant_of_delta_kn mb.mod_delta (Names.KerName.make2 mp lab) in  
       if try ignore (Relations.get_constant arity cst); true with Not_found -> false then 
         continuation ()
       else
       debug_string [`Module] (Printf.sprintf "axiom field: '%s'." (Names.Label.to_string lab));
       declare_realizer ~continuation arity evd env None (mkConst cst)
               
     | (lab, SFBconst cb) ->
       let opaque =     
         match cb.const_body with OpaqueDef _ -> true | _ -> false      
       in
       let kind = Decl_kinds.(Global, cb.const_polymorphic, Definition) in
       let (evdr, env) = ref Evd.empty, Global.env () in
       let cst = Mod_subst.constant_of_delta_kn mb.mod_delta (Names.KerName.make2 mp lab) in  
       if try ignore (Relations.get_constant arity cst); true with Not_found -> false then 
         continuation ()
       else
       let c = Evarutil.e_new_global evdr (Globnames.ConstRef cst) in 
       let lab_R = translate_id arity (Names.Label.to_id lab) in 
       debug [`Module] "field : " env !evdr c;
       (try 
        let typ = Typing.type_of env !evdr c in
        debug [`Module] "type :" env !evdr typ
       with e -> error (Pp.str  (Printexc.to_string e)));
       debug_string [`Module] (Printf.sprintf "constant field: '%s'." (Names.Label.to_string lab));
       declare_abstraction ~opaque ~continuation ~kind arity evdr env c lab_R

     | (lab, SFBmind _) -> 
       let (evd, env) = ref Evd.empty, Global.env () in 
       let mut_ind = Mod_subst.mind_of_delta_kn mb.mod_delta (Names.KerName.make2 mp lab) in 
       let ind = (mut_ind, 0) in 
       if try ignore (Relations.get_inductive arity ind); true with Not_found -> false then 
         continuation ()
       else
       let gind = Evarutil.e_new_global evd (Globnames.IndRef ind) in 
       (try 
        let _, typ =  (Typing.e_type_of env !evd gind) in
        debug [`Module] "type :" env !evd typ
       with e -> error (Pp.str  (Printexc.to_string e)));
       debug [`Module] "field : " env !evd gind;
       debug_string [`Module] (Printf.sprintf "inductive field: '%s'." (Names.Label.to_string lab));
       declare_inductive ~continuation arity evd env ind
   
     | (lab, SFBmodule mb') when 
          match mb'.mod_type with NoFunctor _ ->
            (match mb'.mod_expr with FullStruct | Algebraic _ -> true | _ -> false)
          | _ -> false
        -> declare_module ~continuation arity mb'
     
     | (lab, _) ->
         Pp.(Flags.if_verbose msg_info (str (Printf.sprintf "Ignoring field '%s'." (Names.Label.to_string lab))));
          continuation () 
     ) fields ()
  | Struct _, _ -> error Pp.(str "Module " ++ (str (Names.ModPath.to_string mp)) 
                                 ++ str " is an interactive module.")
  | Abstract, _ -> error Pp.(str "Module " ++ (str (Names.ModPath.to_string mp)) 
                                 ++ str " is an abstract module.")
  | _ -> error Pp.(str "Module " ++ (str (Names.ModPath.to_string mp)) 
                                 ++ str " is not a fully-instantiated module.")

