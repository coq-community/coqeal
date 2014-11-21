open Parametricity
open Vars
open Term
open Constr

(** Adds the definition name := ⟦a⟧ : ⟦b⟧ a a. *)
let declare_abstraction order evd env a b name =
  let sigma = ref evd in 
  Obligations.check_evars env evd;
  debug_string [`Abstraction] "### Begin declaration !";
  debug [`Abstraction] "translate term :" env !sigma a;
  let a_R = translate order sigma env a  in
  debug [`Abstraction] "translate type :" env !sigma b;
  let b_R = relation order sigma env b in 
  let sub = range (fun k -> prime order k a) order in 
  let b_R = substl sub b_R in
  debug [`Abstraction] "translation of term, a_R = " env !sigma a_R;
  debug [`Abstraction] "translation of type, b_R = " env !sigma b_R;
  debug_evar_map [`Abstraction] "type checking  b_R in " !sigma;
  let evd, _ = Typing.e_type_of ~refresh:true env !sigma b_R in
  debug_evar_map [`Abstraction] "type checking  a_R in " evd;
  let evd, b_R' = Typing.e_type_of ~refresh:true env evd a_R in
  debug [`Abstraction] "infered type is b_R' = " env evd b_R';
  debug_string [`Abstraction] "checking cumulativity";
  let evd = Unification.w_unify env evd Reduction.CUMUL b_R' b_R in 
  debug_evar_map [`Abstraction] "after type checking :" evd;
  let obls, _, a_R, b_R = Obligations.eterm_obligations env name evd 0 a_R b_R in 
  let ctx = Evd.evar_universe_context evd in
  let hook = 
    match kind_of_term a with 
      | Const cte -> Some 
         (Lemmas.mk_hook (fun _ dcl -> 
           Pp.(msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name)))); 
            Relations.declare_relation order (Globnames.ConstRef (Univ.out_punivs cte)) dcl))
      | _ -> None
  in
  debug_string [`Abstraction] "add_definition:";
  debug [`Abstraction] "a_R:\t" env !sigma a_R;
  debug [`Abstraction] "b_R:\t" env !sigma b_R;
  ignore (Obligations.add_definition name ?hook ~term:a_R b_R ctx obls)

let translate_command arity c names =  
  let get_constant c = 
    match Term.kind_of_term c with Term.Const cte -> Some cte | _ -> None 
  in
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, c) = Constrintern.interp_open_constr env sigma c in
  let sigma, t = Typing.e_type_of ~refresh:true env sigma c in
  let name =
    match names, get_constant c with
      | None, Some cte -> Names.id_of_string @@ translate_string arity @@ Names.Label.to_string @@ Names.Constant.label @@ Univ.out_punivs cte
      | Some name, _ -> name
      | _ -> Errors.error "In the case of a constant, Abstraction expects 0 or 1 identifier. Otherwise, 1 identifier." 
  in
  declare_abstraction arity sigma env c t name 

let translate_inductive_command arity c name = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, c) = Constrintern.interp_open_constr env sigma c in
  let ((mut_ind, i) as ind, _), _ = Inductive.find_rectype env c in 
  let evd = ref sigma in 
  let mut_body = fst (Inductive.lookup_mind_specif env ind) in
  debug_string [`Inductive] "Translating mind body ..."; 
  let translation_entry = Parametricity.translate_mind_body arity evd env mut_ind mut_body in 
  debug_string [`Inductive] "Translating mind body ... done."; 
  let size = Declarations.(Array.length mut_body.mind_packets) in 
  let _, kn_R = Declare.declare_mind Declare.UserVerbose translation_entry in
  let mut_ind_R = Global.mind_of_delta_kn kn_R in 
  for k = 0 to size-1 do
    Relations.declare_inductive_relation arity (mut_ind, k) (mut_ind_R,k)
  done

let realizer_command arity name var real = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, var) = Constrintern.interp_open_constr env sigma var in
  Obligations.check_evars env sigma;
  let (sigma, real) = Constrintern.interp_open_constr env sigma real in
  let realtyp = Retyping.get_type_of env sigma real in
  let gref = Term.(match kind_of_term var with 
     | Var id -> Globnames.VarRef id 
     | Const (cst, _) -> Globnames.ConstRef cst
     | _ -> Errors.error "Realizer works only for variables and constants.") in 
  let sigma, typ = Typing.e_type_of ~refresh:true env sigma var in
  let evd = ref sigma in 
  let typ_R = Parametricity.relation arity evd env typ in 
  let sub = range (fun _ -> var) arity in 
  let typ_R = Vars.substl sub typ_R in
  ignore (Evarconv.e_cumul env evd realtyp typ_R);
  let kind = Decl_kinds.Global, true, Decl_kinds.Definition in
  let name = match name with Some x -> x | _ -> failwith "TODO: provide a name" in 
  let sigma = !evd in 
  Obligations.check_evars env sigma;
  
  debug [`Realizer] "realtyp =" env sigma realtyp;
  debug [`Realizer] "real =" env sigma real;
  debug [`Realizer] "typ_R =" env sigma typ_R;
  debug_evar_map [`Realizer] "ear_map =" sigma;

  let obls, _, real, typ_R = Obligations.eterm_obligations env name sigma 0 real typ_R in 
  let ctx = Evd.evar_universe_context sigma in
  let hook = Lemmas.mk_hook (fun _ dcl -> 
    Pp.(msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name)))); 
    Relations.declare_relation arity gref dcl) in
  ignore (Obligations.add_definition name ~kind ~term:real ~hook typ_R ctx obls)
