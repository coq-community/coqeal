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


(*i camlp4deps: "src/parametricity.cmo" "src/declare_translation.cmo" i*)

DECLARE PLUGIN "parametricity"
open Parametricity
open Declare_translation


VERNAC COMMAND EXTEND SetParametricityTactic CLASSIFIED AS SIDEFF
| [ "Parametricity" "Tactic" ":=" tactic(t) ] -> [
    Relations.set_parametricity_tactic
      (Locality.make_section_locality (Locality.LocalityFixme.consume ()))
      (Tacintern.glob_tactic t) ]
END


VERNAC COMMAND EXTEND ShowParametricityTactic CLASSIFIED AS QUERY
| [ "Show" "Parametricity" "Tactic" ] -> [
   Pp.(msg_info (str"Paramericity obligation tactic is " ++ Relations.print_parametricity_tactic ())) ]
END


VERNAC COMMAND EXTEND DebugAbstraction CLASSIFIED AS SIDEFF
| [ "DebugParametricity" constr(c)] -> 
  [
    print_translation_command false default_arity c 
  ]
END

VERNAC COMMAND EXTEND DebugAbstractionWithRetyping CLASSIFIED AS SIDEFF
| [ "DebugParametricity" constr(c) "with" "retyping"] -> 
  [
    print_translation_command true default_arity c 
  ]
END



VERNAC COMMAND EXTEND DebugAbstractionWithArity CLASSIFIED AS SIDEFF
| [ "DebugTranslation" constr(c) "arity" integer(arity)] -> 
  [
    print_translation_command false arity c
  ]
END 

VERNAC COMMAND EXTEND Abstraction CLASSIFIED AS SIDEFF
| [ "Parametricity" constr(c) ] -> 
  [
    translate_command default_arity c None  
  ]
END 

VERNAC COMMAND EXTEND AbstractionWithName CLASSIFIED AS SIDEFF
| [ "Parametricity" constr(c) "as" ident(name)] -> 
  [
    translate_command default_arity c (Some name) 
  ] 
END 

VERNAC COMMAND EXTEND AbstractionWithArity CLASSIFIED AS SIDEFF
| [ "Parametricity" constr(c) "arity" integer(arity)] -> 
  [
    translate_command arity c None 
  ]
END

VERNAC COMMAND EXTEND AbstractionWithNameAndarity CLASSIFIED AS SIDEFF
| [ "Parametricity" constr(c) "as" ident(name) "arity" integer(arity)] -> 
  [
    translate_command arity c (Some name) 
  ]
END

VERNAC COMMAND EXTEND TranslateInductive CLASSIFIED AS SIDEFF
| [ "Parametricity" "Inductive" constr(c)  ] ->
  [
    translate_inductive_command default_arity c None
  ]
END

VERNAC COMMAND EXTEND TranslateInductiveWithName CLASSIFIED AS SIDEFF
| [ "Parametricity" "Inductive" constr(c) "as" ident(name)  ] ->
  [
    translate_inductive_command default_arity c (Some name)
  ]
END

VERNAC COMMAND EXTEND TranslateInductiveWithArity CLASSIFIED AS SIDEFF
| [ "Parametricity" "Inductive" constr(c) "arity" integer(arity)  ] ->
  [
    translate_inductive_command arity c None
  ]
END

VERNAC COMMAND EXTEND TranslateInductiveWithNameAndArity CLASSIFIED AS SIDEFF
| [ "Parametricity" "Inductive" constr(c) "as" ident(name) "arity" integer(arity)  ] ->
  [
    translate_inductive_command arity c (Some name)
  ]
END

VERNAC COMMAND EXTEND TranslateModule CLASSIFIED AS SIDEFF
| [ "Parametricity" "Module" global(qid) ] ->
  [
    ignore (translate_module_command Parametricity.default_arity qid)
  ]
END

VERNAC COMMAND EXTEND Test CLASSIFIED AS SIDEFF
| [ "Parametricity" "Test" ] -> 
  [
    Names.(Constr.(
    let program_mode_before = Flags.is_program_mode () in 
    Obligations.set_program_mode !Parametricity.program_mode;
    let env = Global.env () in 
    let evdr = ref Evd.empty in  
    let id_X = Name (id_of_string "X") in 
    let id_x = Name (id_of_string "x") in 
    let id_f = Name (id_of_string "f") in 
    let sort_X = Evarutil.e_new_Type env evdr in 
    let id_type = mkProd (id_x, mkRel 1, mkRel 2) in 
    let id_fun = mkLambda(id_x, mkRel 1, mkRel 1) in  
    let pred = mkLambda (id_f, id_type, Parametricity.CoqConstants.eq evdr
            [| Vars.lift 1 id_type; mkRel 1; mkRel 1 |]) in 
    let term = 
      mkLambda (id_X, sort_X, Parametricity.CoqConstants.transport evdr [| id_type; id_fun; pred |])
    in 
    let term = Typing.solve_evars env evdr term in 
    let name = id_of_string "marc" in 
    let ctx = Evd.evar_universe_context !evdr in
    let typ = Retyping.get_type_of env !evdr term in 
    let obls, _, term, typ = Obligations.eterm_obligations env name !evdr 0 term typ in 
    let kind = Decl_kinds.Global, true, Decl_kinds.Definition in
    ignore (Obligations.add_definition name ~kind ~term:term typ ctx obls);
    Obligations.set_program_mode program_mode_before))
  ]
END

VERNAC COMMAND EXTEND TranslateModuleWithArity CLASSIFIED AS SIDEFF
| [ "Parametricity" "Module" global(qid) "arity" integer(arity) ] ->
  [
    ignore (translate_module_command arity qid)
  ]
END

VERNAC COMMAND EXTEND Realizer CLASSIFIED AS SIDEFF
| [ "Realizer" constr(c) "as" ident(name) ":=" constr(t) ] ->
  [
    realizer_command Parametricity.default_arity (Some name) c t 
  ]
END

VERNAC COMMAND EXTEND RealizerArity CLASSIFIED AS SIDEFF
| [ "Realizer" constr(c) "as" ident(name) "arity" integer(arity) ":=" constr(t) ] ->
  [
    realizer_command arity (Some name) c t 
  ]
END
