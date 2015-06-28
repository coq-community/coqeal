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

VERNAC COMMAND EXTEND ShowTable CLASSIFIED AS QUERY
| [ "Show" "Parametricity" "Table" ] -> [
  Relations.print_relations ()
]
END

VERNAC COMMAND EXTEND ShowParametricityTactic CLASSIFIED AS QUERY
| [ "Show" "Parametricity" "Tactic" ] -> [
   Pp.(msg_info (str "Paramericity obligation tactic is " ++ Relations.print_parametricity_tactic ())) ]
END

VERNAC COMMAND EXTEND ParametricityDefined CLASSIFIED AS SIDEFF
| [ "Parametricity" "Done"  ] -> [
    parametricity_close_proof ()
]
END

VERNAC COMMAND EXTEND AbstractionReference CLASSIFIED AS SIDEFF
| [ "Parametricity" reference(c) ] -> 
  [
    command_reference default_arity (Constrintern.intern_reference c) None  
  ]
| [ "Parametricity" reference(c) "as" ident(name)] -> 
  [
    command_reference default_arity (Constrintern.intern_reference c) (Some name)
  ]
| [ "Parametricity" reference(c) "arity" integer(arity) ] -> 
  [
    command_reference arity (Constrintern.intern_reference c) None  
  ]
| [ "Parametricity" reference(c) "arity" integer(arity) "as" ident(name) ] ->
  [
    command_reference arity (Constrintern.intern_reference c) (Some name)  
  ]
| [ "Parametricity" reference(c)  "as" ident(name) "arity" integer(arity) ] -> 
  [
    command_reference arity (Constrintern.intern_reference c) (Some name)  
  ]
END 

VERNAC COMMAND EXTEND AbstractionRecursive CLASSIFIED AS SIDEFF
| [ "Parametricity" "Recursive" reference(c) ] -> 
  [
    command_reference_recursive default_arity (Constrintern.intern_reference c)
  ]
| [ "Parametricity" "Recursive" reference(c) "arity" integer(arity) ] -> 
  [
    command_reference_recursive arity (Constrintern.intern_reference c)
  ]
END

VERNAC COMMAND EXTEND Abstraction CLASSIFIED AS SIDEFF
| [ "Parametricity" "Translation" constr(c) "as" ident(name)] -> 
  [
    translate_command default_arity c name
  ] 
| [ "Parametricity" "Translation" constr(c) "as" ident(name) "arity" integer(arity) ] -> 
  [
    translate_command arity c name 
  ]
| [ "Parametricity" "Translation" constr(c) "arity" integer(arity) "as" ident(name)] -> 
  [
    translate_command arity c name 
  ]
END

VERNAC COMMAND EXTEND TranslateModule CLASSIFIED AS SIDEFF
| [ "Parametricity" "Module" global(qid) ] ->
  [
    ignore (translate_module_command Parametricity.default_arity qid)
  ]
| [ "Parametricity" "Module" global(qid) "as" ident(name) ] ->
  [
    ignore (translate_module_command ~name Parametricity.default_arity qid)
  ]
| [ "Parametricity" "Module" global(qid) "arity" integer(arity) ] ->
  [
    ignore (translate_module_command arity qid)
  ]
| [ "Parametricity" "Module" global(qid) "as" ident(name) "arity" integer(arity) ] ->
  [
    ignore (translate_module_command ~name arity qid)
  ]
| [ "Parametricity" "Module" global(qid) "arity" integer(arity) "as" ident(name)] ->
  [
    ignore (translate_module_command ~name arity qid)
  ]
END

VERNAC COMMAND EXTEND Realizer CLASSIFIED AS SIDEFF
| [ "Realizer" constr(c) "as" ident(name) ":=" constr(t) ] ->
  [
    realizer_command Parametricity.default_arity (Some name) c t 
  ]
| [ "Realizer" constr(c) "as" ident(name) "arity" integer(arity) ":=" constr(t) ] ->
  [
    realizer_command arity (Some name) c t 
  ]
| [ "Realizer" constr(c) "arity" integer(arity) "as" ident(name) ":=" constr(t) ] ->
  [
    realizer_command arity (Some name) c t 
  ]
END
