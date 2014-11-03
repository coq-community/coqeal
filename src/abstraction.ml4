(**************************************************************************)
(*                                                                        *)
(*     CoqParam                                                           *)
(*     Copyright (C) 2012                                                 *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*     Marc Lasson                                                        *)
(*                                                                        *)
(*     INRIA - École Polytechnique - ÉNS de Lyon                          *)
(*                                                                        *)
(*   This file is distributed under the terms of the GNU Lesser General   *)
(*   Public License                                                       *)
(*                                                                        *)
(**************************************************************************)


DECLARE PLUGIN "parametricity"
open Parametricity

VERNAC COMMAND EXTEND Unfolded CLASSIFIED AS SIDEFF
| [ "Unfold" "Fixpoint" constr(c) ident(name) ] -> 
  [
    let (evd, env) = Lemmas.get_current_context () in 
    let (evd, c) = Constrintern.interp_open_constr evd env c in
    let evdref = ref evd in
    let goal = unfold_fixpoint_statement evdref env c in 
    let evd = !evdref in
    Obligations.check_evars env evd;
    let evd, hole = Evarutil.new_evar evd env goal in
    let obls, _, hole, goal = Obligations.eterm_obligations env name evd 0 hole goal in 
    let ctx = Evd.evar_universe_context evd in
    ignore (Obligations.add_definition name ~term:hole goal ctx obls)
  ]
END


let translate_command arity c names =  
  let get_constant c = 
    match Term.kind_of_term c with Term.Const cte -> Some cte | _ -> None 
  in
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, c) = Constrintern.interp_open_constr sigma env c in
  let sigma, t = Typing.e_type_of env sigma c in
  let name =
    match names, get_constant c with
      | None, Some cte -> Names.id_of_string @@ translate_string arity @@ Names.Label.to_string @@ Names.Constant.label @@ Univ.out_punivs cte
      | Some name, _ -> name
      | _ -> failwith "In the case of a constant, Abstraction expects 0 or 1 identifier. Otherwise, 1 identifier." 
  in
  declare_abstraction arity sigma env c t name 


VERNAC COMMAND EXTEND Abstraction CLASSIFIED AS SIDEFF
| [ "Translate" constr(c) ] -> 
  [
    translate_command default_arity c None  
  ]
END 
VERNAC COMMAND EXTEND AbstractionWithName CLASSIFIED AS SIDEFF
| [ "Translate" constr(c) "as" ident(name)] -> 
  [
    translate_command default_arity c (Some name) 
  ] 
END 
VERNAC COMMAND EXTEND AbstractionWithArity CLASSIFIED AS SIDEFF
| [ "Translate" constr(c) "Arity" integer(arity)] -> 
  [
    translate_command arity c None 
  ]
END
VERNAC COMMAND EXTEND AbstractionWithNameAndArity CLASSIFIED AS SIDEFF
| [ "Translate" constr(c) "as" ident(name) "Arity" integer(arity)] -> 
  [
    translate_command arity c (Some name) 
  ]
END

let translate_inductive_command arity c name = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, c) = Constrintern.interp_open_constr sigma env c in
  let ((mut_ind, i) as ind, _), _ = Inductive.find_rectype env c in 
  Pp.msg_notice (Pp.str (string_of_int i));
  let evd = ref sigma in 
  print_string "ear_map ="; Pp.msg_info (Evd.pr_evar_map None sigma);
  let mut_body = fst (Inductive.lookup_mind_specif env ind) in
  let translation_entry = Parametricity.translate_mind_body arity evd env mut_ind mut_body in 
  print_string "ear_map ="; Pp.msg_info (Evd.pr_evar_map None !evd);
  let _, kn_R = Declare.declare_mind Declare.UserVerbose translation_entry in
  let mut_ind_R = Global.mind_of_delta_kn kn_R in 
  Relations.add_inductive arity mut_ind mut_ind_R


VERNAC COMMAND EXTEND TranslateInductive CLASSIFIED AS SIDEFF
| [ "Translate" "Inductive" constr(c)  ] ->
  [
    translate_inductive_command default_arity c None
  ]
END

VERNAC COMMAND EXTEND TranslateInductiveWithArity CLASSIFIED AS SIDEFF
| [ "Translate" "Inductive" constr(c) "Arity" integer(arity)  ] ->
  [
    translate_inductive_command arity c None
  ]
END

let define_realizer arity name var real = 
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, var) = Constrintern.interp_open_constr sigma env var in
  Obligations.check_evars env sigma;
  let (sigma, real) = Constrintern.interp_open_constr sigma env real in
  let realtyp = Retyping.get_type_of env sigma real in
  Term.(match kind_of_term var with 
   | Var id -> 
     let evd = ref sigma in 
     let typ = Environ.named_type id env in 
     let typ_R = Parametricity.relation arity evd env typ in 
     let sub = range (fun _ -> var) arity in 
     let typ_R = Vars.substl sub typ_R in
     (* evd := Unification.w_unify env !evd Reduction.CUMUL realtyp typ_R; *)
     ignore (Evarconv.e_cumul env evd realtyp typ_R);
     let kind = Decl_kinds.Global, true, Decl_kinds.Definition in
     let name = match name with Some x -> x | _ -> failwith "TODO: provide a name" in 
     let sigma = !evd in 
     Obligations.check_evars env sigma;
     
     print_string "realtyp ="; debug env realtyp;
     print_string "real ="; debug env real;
     print_string "typ_R ="; debug env typ_R;
     print_string "ear_map ="; Pp.msg_info (Evd.pr_evar_map None sigma);

     let obls, _, real, typ_R = Obligations.eterm_obligations env name sigma 0 real typ_R in 
     let ctx = Evd.evar_universe_context sigma in
     let hook = Lemmas.mk_hook (fun _ dcl -> Relations.add_global arity (Globnames.VarRef id) dcl) in
     ignore (Obligations.add_definition name ~kind ~term:real ~hook typ_R ctx obls)
   | _ -> failwith "not a variable")

VERNAC COMMAND EXTEND Realizer CLASSIFIED AS SIDEFF
| [ "Realizer" constr(c) "As" ident(name) ":=" constr(t) ] ->
  [
    define_realizer Parametricity.default_arity (Some name) c t 
  ]
END

VERNAC COMMAND EXTEND TestObligation CLASSIFIED AS SIDEFF
| [ "TestObligation" ident(name) constr(c) ] -> 
  [
    let (evd, env) = Lemmas.get_current_context () in 
    let (evd, c) = Constrintern.interp_open_constr evd env c in
    Obligations.check_evars env evd;
    let cty = Retyping.get_type_of env evd c in 
    let obls, _, c, cty = Obligations.eterm_obligations env name evd 0 c cty in 
    let ctx = Evd.evar_universe_context evd in
    ignore (Obligations.add_definition name ~term:c cty ctx obls)
  ]
| [ "Test" constr(c) ] ->
  [
    let (sigma, env) = Lemmas.get_current_context () in 
    let (sigma, c) = Constrintern.interp_open_constr sigma env c in
    Pp.msg_notice (Pp.str "starting test ...");
    Parametricity.test := c;
    Parametricity.debug Environ.empty_env c
  ]
(*
| [ "Test" ] ->
  [
    let test_case = Term.mkArrow (Term.mkRel 1) (Term.mkRel 2) in
    Parametricity.debug Environ.empty_env test_case;
    let test_case_R = Parametricity.relation Parametricity.default_arity Environ.empty_env test_case in 
    Parametricity.debug Environ.empty_env test_case_R
  ] *)

END

VERNAC COMMAND EXTEND Helloworld CLASSIFIED AS SIDEFF
| [ "PrintTranslation" constr(c) ] ->
  [
    let order = Parametricity.default_arity in 
    let (sigma, env) = Lemmas.get_current_context () in 
    let (sigma, c) = Constrintern.interp_open_constr sigma env c in
    let sigma, t = Typing.e_type_of env sigma c in
    let evd = ref sigma in
    let c_R = Parametricity.translate order evd env c in 
    let t_R = relation order evd env t in 
    let sub = range (fun k -> prime order k c) order in 
    let t_R = Vars.substl sub t_R in
    Pp.msg_notice (Pp.str "#### translation of term :");
    Pp.msg_notice (Printer.pr_constr_goal_style_env env c);
    Pp.msg_notice (Pp.str "####");
    Pp.msg_notice (Printer.pr_constr_goal_style_env env c_R);
    Pp.msg_notice (Pp.str "#### translation of type :");
    Pp.msg_notice (Printer.pr_constr_goal_style_env env t);
    Pp.msg_notice (Pp.str "####");
    Pp.msg_notice (Printer.pr_constr_goal_style_env env t_R)
  ]
END 


