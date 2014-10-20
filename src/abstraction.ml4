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

open Parametricity

DECLARE PLUGIN "parametricity"

VERNAC COMMAND EXTEND Unfolded CLASSIFIED AS SIDEFF
| [ "Unfold" "Fixpoint" constr(c) ident(name) ] -> 
  [
    let (evd, env) = Lemmas.get_current_context () in 
    let (evd, c) = Constrintern.interp_open_constr evd env c in
    let goal = unfold_fixpoint_statement env c in 
    Obligations.check_evars env evd;
    let evd, hole = Evarutil.new_evar evd env goal in
    let obls, _, hole, goal = Obligations.eterm_obligations env name evd 0 hole goal in 
    let ctx = Evd.evar_universe_context evd in
    ignore (Obligations.add_definition name ~term:hole goal ctx obls)
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
    let (sigma, env) = Lemmas.get_current_context () in 
    let (sigma, c) = Constrintern.interp_open_constr sigma env c in
    Pp.msg_notice (Printer.pr_constr_goal_style_env env c);
    let c_R = Parametricity.translate Parametricity.default_arity (ref sigma) env c in 
    Pp.msg_notice (Printer.pr_constr_goal_style_env env c_R)
  ]
END 

let translate_command arity c names =  
  let get_constant c = 
    match Term.kind_of_term c with Term.Const cte -> Some cte | _ -> None 
  in
  let (sigma, env) = Lemmas.get_current_context () in 
  let (sigma, c) = Constrintern.interp_open_constr sigma env c in
  let t = Retyping.get_type_of env sigma c in
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
  let mut_body = fst (Inductive.lookup_mind_specif env ind) in
  let translation_entry = translate_mind_body arity evd env mut_ind mut_body in 
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
