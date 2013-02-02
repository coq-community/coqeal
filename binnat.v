(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import ZArith.
Require Import refinements.

(******************************************************************************)
(* The binary naturals of Coq is a refinement of SSReflects naturals (ssrnat) *) 
(*                                                                            *)
(* ??? == some documentation                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section binnat.

(* Definition nat_of_N (n : N) := Some (nat_of_bin n). *)

Lemma N_of_natK : pcancel bin_of_nat ((@Some nat) \o nat_of_bin).
Proof.
by move=> n /=; rewrite bin_of_natK.
(* by rewrite /nat_of_N => n /=; rewrite bin_of_natK. *)
Qed.

Global Instance refinement_nat_N : refinement_of nat N := Refinement N_of_natK.

(* Constants *)
Global Program Instance zero_N : zero N := 0%N.
Global Program Instance refines_nat_0 : refines 0%nat 0%C.

Global Program Instance one_N : one N := 1%N.
Global Program Instance refines_nat_1 : refines 1%nat 1%C.

(* Unary operations *)
(* Global Program Instance opp_N : opp N := N.opp. *)
(* Global Program Instance refines_int_opp (x : int) (x' : Z) *)
(*   (rx : refines x x') : refines (- x) (- x')%C. *)
(* Next Obligation. Admitted. *)

(* Binary operations *)
Global Program Instance add_N : add N := N.add.
Global Program Instance refines_nat_add (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x + y)%nat (x' + y')%C.
Next Obligation.
by rewrite -[x]specd_refines -[y]specd_refines nat_of_add_bin.
Qed.

(* TODO: Finish! *)
Global Program Instance sub_N : sub N := N.sub. 
Global Program Instance refines_nat_sub (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x - y)%nat (x' - y')%C.
Next Obligation.
rewrite -[x]specd_refines -[y]specd_refines.
admit.
Qed.

Global Program Instance mul_N : mul N := N.mul.
Global Program Instance refines_nat_mul (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x * y)%nat (x' * y')%C. 
Next Obligation. 
by rewrite -[x]specd_refines -[y]specd_refines nat_of_mul_bin.
Qed.

(* Comparison operations *)
Global Program Instance eq_N : eq N := N.eqb.
Global Program Instance refines_nat_eq (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x == y) (x' == y')%C.
Next Obligation.
congr Some; rewrite -[x]specd_refines -[y]specd_refines /specd /eq_op /eq_N /=.
case: (N.eqb_spec _ _) => [->|/eqP hneq]; first by rewrite eqxx.
by apply/esym/negbTE/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

Global Program Instance leq_N : leq N := N.leb.
Global Program Instance refines_nat_leq (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x <= y) (x' <= y')%C.
Next Obligation.
congr Some.
case: (refines_nat_sub _ _ _ _ rx ry) => /= H. (* ARGH! *)
move: (Some_inj H). (* Why can't I just do "=> /= /Some_inj" above??? *)
rewrite -[x]specd_refines -[y]specd_refines /specd /= /leq_op /leq_N => {H} H.
case: (N.leb_spec0 _ _) => [/N.sub_0_le|] h.
  apply/esym/eqP.
  by rewrite -H /sub_op /sub_N h.
apply/esym/negbTE/negP => [/eqP].
rewrite -H.
have -> : 0 = nat_of_bin 0 by []. (* HMM... *)
by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

Global Program Instance lt_N : lt N := N.ltb.
Global Program Instance refines_nat_lt (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x < y) (x' < y')%C.
Next Obligation. 
congr Some.
rewrite /lt_op /lt_N N.ltb_antisym.
case: (refines_nat_leq _ _ _ _ ry rx); rewrite /= /leq_op /leq_N => h. (* ARGH! *)
by rewrite (Some_inj h) -ltnNge.
Qed.

(* Global Program Instance geq_N : geq N := N.ge. *)
(* Global Program Instance refines_nat_geq (x y : nat) (x' y' : N) *)
(*   (rx : refines x x') (ry : refines y y') : refines (x >= y) (x' >= y')%C. *)
(* Next Obligation. Admitted. *)

(* Global Program Instance gt_N : gt N := N.gtb. *)
(* Global Program Instance refines_nat_gt (x y : nat) (x' y' : N) *)
(*   (rx : refines x x') (ry : refines y y') : refines (x > y) (x' > y')%C. *)
(* Next Obligation. Admitted. *)

End binnat.

(* (* Some tests *) *)
(* Eval compute in 0%C. *)
(* Eval compute in (1 + 1 * 1 + 1)%C. *)