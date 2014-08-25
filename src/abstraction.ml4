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

VERNAC COMMAND EXTEND Helloworld CLASSIFIED AS SIDEFF
| [ "Hello" ] ->
  [
    Pp.msg_info (Pp.str "Hello world !")
  ]
| [ "Hello" constr(c) ] ->
  [
    Pp.msg_notice (Ppconstr.pr_constr_expr c)
  ]
END 


