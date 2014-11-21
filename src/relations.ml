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


open Term
open Names
open Globnames
open Libobject

module IntMap = Map.Make(Int)
module GMap = Map.Make(Globnames.RefOrdered)

let initial_translations = GMap.empty
let initial_relations = IntMap.empty

let relations = Summary.ref initial_relations ~name:"parametricity"

let add (n : int) f = 
  let translations =
    try IntMap.find n !relations with Not_found -> initial_translations
  in
  relations := IntMap.add n (f translations) !relations

let cache_relation (_, (n, x, x_R)) = 
  add n (GMap.add x x_R)

let discharge_relation (_, (n, x, x_R)) = 
  Some (n, Lib.discharge_global x, Lib.discharge_global x_R)

let subst_relation (subst, (n, x, x_R)) = 
    (n, subst_global_reference subst x, subst_global_reference subst x_R)

let in_relation = declare_object {(default_object "PARAMETRICITY") with 
                   cache_function = cache_relation;
                   load_function = (fun _ -> cache_relation);
                   subst_function = subst_relation;
                   classify_function = (fun obj -> Substitute obj);
                   discharge_function = discharge_relation}
 
let declare_relation n x x_R = 
 Lib.add_anonymous_leaf (in_relation (n, x, x_R))
 
let declare_constant_relation (n : int) (c : constant) (c_R : constant) = 
  declare_relation n (ConstRef c) (ConstRef c_R)

let declare_inductive_relation (n : int) (i : inductive) (i_R : inductive) = 
  declare_relation n (IndRef i) (IndRef i_R)

let declare_variable_relation (n : int) (v : variable) (v_R : constant) = 
  declare_relation n (VarRef v) (ConstRef v_R)

let get_constant n c = 
  let map = IntMap.find n !relations in
  destConstRef (GMap.find (ConstRef c) map)

let get_inductive n i = 
  let map = IntMap.find n !relations in
  destIndRef (GMap.find (IndRef i) map)

let get_variable n v = 
  let map = IntMap.find n !relations in
  destConstRef (GMap.find (VarRef v) map)
  

