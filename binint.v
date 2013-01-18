(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import ZArith.
Require Import refinements.

(******************************************************************************)
(* The binary integers of Coq is a refinement of SSReflects integers (ssrint) *) 
(*                                                                            *)
(* ??? == some documentation                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.

Section binint.

Definition Z_of_int (m : int) : Z := match m with
  | Posz m' => Z_of_nat m'
  | Negz m' => (- Z_of_nat (m'.+1))%Z
  end.

Definition int_of_Z (m : Z) : option int := match m with
  | Z0 => Some 0
  | Zpos p => Some (Pos.to_nat p)%:Z
  | Zneg p => Some (- (Pos.to_nat p)%:Z)
  end.

Lemma Z_of_intK : pcancel Z_of_int int_of_Z.
Proof.
by rewrite /Z_of_int /int_of_Z => [[[]|]] //= n; rewrite SuccNat2Pos.id_succ.
Qed.

Global Instance refinement_int_Z : refinement_of int Z := Refinement Z_of_intK.

(* Constants *)
Global Program Instance zero_Z : zero Z := 0%Z.
Global Program Instance refines_int_0 : refines 0%R 0%Z.

Global Program Instance one_Z : one Z := 1%Z.
Global Program Instance refines_int_1 : refines 1%R 1%Z.

(* Unary operations *)
Global Program Instance opp_Z : opp Z := Z.opp.
Global Program Instance refines_int_opp (x : int) (x' : Z)
  (rx : refines x x') : refines (- x) (- x')%C.
Next Obligation. Admitted.

(* Binary operations *)
Global Program Instance add_Z : add Z := Z.add.
Global Program Instance refines_int_add (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x + y) (x' + y')%C.
Next Obligation. Admitted.

Global Program Instance sub_Z : sub Z := Z.sub.
Global Program Instance refines_int_sub (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x - y) (x' - y')%C.
Next Obligation. Admitted.

Global Program Instance mul_Z : mul Z := Z.mul.
Global Program Instance refines_int_mul (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x * y) (x' * y')%C. 
Next Obligation. Admitted.

(* Comparison operations *)
Global Program Instance eq_Z : eq Z := Z.eqb.
Global Program Instance refines_int_eq (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x == y) (x' == y')%C.
Next Obligation.
rewrite /eq_op /eq_Z; case: (Z.eqb_spec _ _) => h.
  suff: (Some x == Some y) by move/eqP => h'; rewrite (Some_inj h') eqxx.
  by rewrite -!spec_refines h.
admit.
(* by rewrite -[LHS]id_refines_implem eq_xy id_refines_implem. *)
Qed.

Global Program Instance leq_Z : leq Z := Z.leb.
Global Program Instance refines_int_leq (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x <= y) (x' <= y')%C.
Next Obligation. Admitted.

Global Program Instance lt_Z : lt Z := Z.ltb.
Global Program Instance refines_int_lt (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x < y) (x' < y')%C.
Next Obligation. Admitted.

Global Program Instance geq_Z : geq Z := Z.geb.
Global Program Instance refines_int_geq (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x >= y) (x' >= y')%C.
Next Obligation. Admitted.

Global Program Instance gt_Z : gt Z := Z.gtb.
Global Program Instance refines_int_gt (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x > y) (x' > y')%C.
Next Obligation. Admitted.

End binint.

(* (* Some tests *) *)
(* Eval compute in 0%C. *)
(* Eval compute in (1 + 1 * 1 + 1)%C. *)