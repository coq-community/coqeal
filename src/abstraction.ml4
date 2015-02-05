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
    print_translation_command default_arity c 
  ]
END

VERNAC COMMAND EXTEND DebugAbstractionWithArity CLASSIFIED AS SIDEFF
| [ "DebugTranslation" constr(c) "arity" integer(arity)] -> 
  [
    print_translation_command arity c
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
