open Parametricity
open Vars
open Term
open Constr
open Libnames

let obligation_message () =  
  let open Pp in 
  msg_notice (str "The parametricity tactic generated generated proof obligations."
          ++  str "Please prove them and end your proof with 'Parametricity Done'.")

let default_continuation = ignore

let add_definition ~opaque ~hook ~kind ~tactic name env evd term typ = 
  Parametricity.debug Parametricity.all "add_definition, term = " env evd (snd (term ( evd)));
  Parametricity.debug Parametricity.all "add_definition, typ  = " env evd typ;
  Parametricity.debug_evar_map Parametricity.all "add_definition, evd  = " evd;
  let init_tac = 
    let open Proofview in 
    let unsafe = true in
    tclTHEN (Refine.refine ~unsafe term) tactic 
  in 
  let open Proof_global in
  let open Vernacexpr in 
  let opacity = if opaque then Opaque None else Transparent in 
  Lemmas.start_proof name ~init_tac kind evd typ hook;
  let proof = Proof_global.give_me_the_proof () in 
  let is_done = Proof.is_done proof in 
  if is_done then
    begin
      let proof_obj, terminator = Proof_global.close_proof ~keep_body_ucst_sepatate:false (fun x -> x) in 
      Pfedit.delete_current_proof ();
      terminator (Proof_global.Proved (opacity,None,proof_obj))
    end
  else 
    obligation_message ()

let declare_abstraction ?(opaque = false) ?(continuation = default_continuation) ?kind arity evdr env a name = 
  Parametricity.debug_evar_map Parametricity.all "declare_abstraction, evd  = " !evdr;
  let program_mode_before = Flags.is_program_mode () in 
  Obligations.set_program_mode !Parametricity.program_mode;
  debug [`Abstraction] "declare_abstraction, a =" env !evdr a;
  let b = Retyping.get_type_of env !evdr a in
  debug [`Abstraction] "declare_abstraction, b =" env !evdr b;
  let b = Retyping.get_type_of env !evdr a in
  let b_R = relation arity evdr env b in 
  let sub = range (fun k -> prime arity k a) arity in 
  let b_R = substl sub b_R in
  let a_R = fun evd -> 
    let evdr = ref evd in 
    let a_R = translate arity evdr env a in 
    debug [`Abstraction] "a_R = " env !evdr a_R;
    debug_evar_map Parametricity.all "abstraction, evar_map =" !evdr;
    !evdr, a_R 
  in 
  let evd = !evdr in
  let hook = 
    match kind_of_term a with 
      | Const cte when 
          (try ignore (Relations.get_constant arity (Univ.out_punivs cte)); false with Not_found -> true)
        -> 
         (Lemmas.mk_hook (fun _ dcl -> 
           Pp.(Flags.if_verbose msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name)))); 
            Relations.declare_relation arity (Globnames.ConstRef (Univ.out_punivs cte)) dcl; 
            continuation ()))
      | _ -> (Lemmas.mk_hook (fun _ dcl -> continuation ()))
  in
  let kind = match kind with 
                 None -> Decl_kinds.Global, true, Decl_kinds.DefinitionBody Decl_kinds.Definition 
           | Some kind -> kind in 
  let tactic = snd (Relations.get_parametricity_tactic ()) in 
  add_definition ~tactic ~opaque ~kind ~hook name env evd a_R b_R;
  Obligations.set_program_mode program_mode_before


let declare_inductive ?(continuation = default_continuation) arity evd env (((mut_ind, _) as ind, inst)) = 
  let mut_body, _ = Inductive.lookup_mind_specif env ind in
  debug_string [`Inductive] "Translating mind body ..."; 
  let translation_entry = Parametricity.translate_mind_body arity evd env mut_ind mut_body inst in 
  debug_string [`Inductive] "Translating mind body ... done."; 
  debug_evar_map [`Inductive] "evar_map inductive " !evd;
  let size = Declarations.(Array.length mut_body.mind_packets) in 
  let mut_ind_R = Command.declare_mutual_inductive_with_eliminations translation_entry [] in
  for k = 0 to size-1 do
    Relations.declare_inductive_relation arity (mut_ind, k) (mut_ind_R,k)
  done; 
  continuation ()

let translate_inductive_command arity c name = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, c) = Constrintern.interp_open_constr env sigma c in
  let (ind, _) as pind, _ =
    try 
      Inductive.find_rectype env c
    with Not_found -> 
      error (Pp.(str "Unable to locate an inductive in " ++ Printer.pr_constr_env env sigma c))
  in
  try
    let ind_R = Globnames.destIndRef (Relations.get_inductive arity ind) in 
    error (Pp.(str "The inductive " ++ Printer.pr_inductive env ind ++ str " already as the following registered translation " ++ Printer.pr_inductive env ind_R))
  with Not_found -> 
  let evd = ref sigma in 
  declare_inductive arity evd env pind

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
  let cpt = ref 0 in
  let real = 
    incr cpt;
    match real with Some real -> fun sigma -> 
      let (sigma, term) = real sigma in 
      let realtyp = Retyping.get_type_of env sigma term in
      debug [`Realizer] (Printf.sprintf "real in realdef (%d) =" !cpt) env sigma term;
      debug [`Realizer] (Printf.sprintf "realtyp in realdef (%d) =" !cpt) env sigma realtyp;
      let evdr = ref sigma in 
      ignore (Evarconv.e_cumul env evdr realtyp typ_R); 
      let nf, _ = Evarutil.e_nf_evars_and_universes evdr in 
      let term = nf term in 
      debug [`Realizer] (Printf.sprintf "real in realdef (%d), after =" !cpt) env !evdr term;
      debug [`Realizer] (Printf.sprintf "realtyp in realdef (%d), after =" !cpt) env !evdr realtyp;
      (!evdr, term)
    | None -> fun sigma ->
      (let sigma, real = Evarutil.new_evar env sigma typ_R in 
      (sigma, real))
  in
  let kind = Decl_kinds.Global, true, Decl_kinds.DefinitionBody Decl_kinds.Definition in
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
  let hook = Lemmas.mk_hook (fun _ dcl -> 
    Pp.(msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name)))); 
    Relations.declare_relation arity gref dcl; 
    continuation ()) in
  let tactic = snd (Relations.get_parametricity_tactic ()) in 
  add_definition ~tactic  ~opaque:false ~kind ~hook name env sigma real typ_R
  
let realizer_command arity name var real = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, var) = Constrintern.interp_open_constr env sigma var in
  Obligations.check_evars env sigma;
  let real = fun sigma -> Constrintern.interp_open_constr env sigma real in
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
  debug_string [`Module] "--> declare_module";
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
       let kind = Decl_kinds.(Global, cb.const_polymorphic, DefinitionBody Definition) in
       let (evdr, env) = ref Evd.empty, Global.env () in
       let cst = Mod_subst.constant_of_delta_kn mb.mod_delta (Names.KerName.make2 mp lab) in  
       if try ignore (Relations.get_constant arity cst); true with Not_found -> false then 
         continuation ()
       else
       let evd, ucst = 
          Evd.(with_context_set univ_rigid !evdr (Universes.fresh_constant_instance env cst))
       in 
       let c = mkConstU ucst in
       evdr := evd;
       let lab_R = translate_id arity (Names.Label.to_id lab) in 
       debug [`Module] "field : " env !evdr c;
       (try 
        let typ = Typing.type_of env !evdr c in
        debug [`Module] "type :" env !evdr typ
       with e -> error (Pp.str  (Printexc.to_string e)));
       debug_string [`Module] (Printf.sprintf "constant field: '%s'." (Names.Label.to_string lab));
       declare_abstraction ~opaque ~continuation ~kind arity evdr env c lab_R

     | (lab, SFBmind _) -> 
       let (evdr, env) = ref Evd.empty, Global.env () in 
       let mut_ind = Mod_subst.mind_of_delta_kn mb.mod_delta (Names.KerName.make2 mp lab) in 
       let ind = (mut_ind, 0) in 
       if try ignore (Relations.get_inductive arity ind); true with Not_found -> false then 
         continuation ()
       else begin
         let evd, pind = 
            Evd.(with_context_set univ_rigid !evdr (Universes.fresh_inductive_instance env ind))
         in 
         evdr := evd;
         debug_string [`Module] (Printf.sprintf "inductive field: '%s'." (Names.Label.to_string lab));
         declare_inductive ~continuation arity evdr env pind
       end
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


let command_variable arity variable names = failwith "command_variable"

let command_constant arity constant names = 
  let poly, opaque = 
    let cb = Global.lookup_constant constant in 
    Declarations.(cb.const_polymorphic, match cb.const_body with Def _ -> false | _ -> true)
  in 
  let name = match names with
      | None -> 
             Names.id_of_string 
          @@ translate_string arity 
          @@ Names.Label.to_string 
          @@ Names.Constant.label 
          @@ constant
      | Some name -> name
  in
  let kind = Decl_kinds.(Global, poly, DefinitionBody Definition) in
  let (evd, env) = Lemmas.get_current_context () in 
  let evd, pconst = 
    Evd.(with_context_set univ_rigid evd (Universes.fresh_constant_instance env constant))
  in 
  let constr = mkConstU pconst in 
  declare_abstraction ~opaque ~kind arity (ref evd) env constr name

let command_inductive arity inductive names = 
  let (evd, env) = Lemmas.get_current_context () in 
  let evd, pind = 
    Evd.(with_context_set univ_rigid evd (Universes.fresh_inductive_instance env inductive))
  in 
  declare_inductive arity (ref evd) env pind


let command_constructor arity constructor names = failwith "command_constructor"

let command_reference arity gref names = 
   Pp.(msg_info (str "Using command_reference !"));
   let open Globnames in
   match gref with 
   | VarRef variable -> command_variable arity variable names
   | ConstRef constant -> command_constant arity constant names
   | IndRef inductive -> command_inductive arity inductive names
   | ConstructRef constructor -> command_constructor arity constructor names
  

let translate_command arity c name =  
  let open Constrexpr in
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
  let kind = Decl_kinds.(Global, poly, DefinitionBody Definition) in
  declare_abstraction ~opaque ~kind arity (ref evd) env c name 


