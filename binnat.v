(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import ZArith.
Require Import refinements.

(******************************************************************************)
(* The binary naturals of Coq is a refinement of SSReflects naturals (ssrnat) *) 
(*                                                                            *)
(* Supported operations are: 0, 1, +, *, ==                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation N := N.

Section binnat.

Lemma N_of_natK : pcancel bin_of_nat (some \o nat_of_bin).
Proof. by move=> n /=; rewrite bin_of_natK. Qed.

Global Instance refinement_nat_N : refinement nat N := Refinement N_of_natK.

Lemma refines_natE (n : nat) (x : N) : refines n x -> n = x. 
Proof. by case. Qed.

(* Constants *)
Global Instance zero_N : zero N := 0%N.
Global Program Instance refines_nat_0 : refines 0%nat 0%C.

Global Instance one_N : one N := 1%N.
Global Program Instance refines_nat_1 : refines 1%nat 1%C.

(* Binary operations *)
Global Instance add_N : add N := N.add.
Global Program Instance refines_nat_add (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x + y)%nat (x' + y')%C.
Obligation 1. by rewrite [x]refines_natE [y]refines_natE nat_of_add_bin. Qed.

(* TODO: Finish! *)
Global Instance sub_N : sub N := N.sub.
Global Program Instance refines_nat_sub (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x - y)%nat (x' - y')%C.
Next Obligation.
rewrite [x]refines_natE [y]refines_natE.
admit.
Qed.

Global Instance mul_N : mul N := N.mul.
Global Program Instance refines_nat_mul (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x * y)%nat (x' * y')%C. 
Obligation 1. by rewrite [x]refines_natE [y]refines_natE nat_of_mul_bin. Qed.

(* Comparison operations *)
Global Instance eq_N : eq N := N.eqb.
Global Instance refines_nat_eq (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x == y) (x' == y')%C.
Proof.
congr Some; rewrite [x]refines_natE [y]refines_natE /eq_op /eq_N.
case: (N.eqb_spec _ _) => [->|/eqP hneq]; first by rewrite eqxx.
by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

Global Instance leq_N : leq N := N.leb.
Global Instance refines_nat_leq (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x <= y) (x' <= y')%C.
Proof.
congr Some; rewrite /leq_op /leq_N.
case: (N.leb_spec0 _ _) => [/N.sub_0_le|] /= h.
  by apply/eqP; rewrite [_ - _]refines_natE  [(_ - _)%C]h.
apply/negP => /eqP; rewrite [_ - _]refines_natE [0]refines_natE.
by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

Global Instance lt_N : lt N := N.ltb.
Global Instance refines_nat_lt (x y : nat) (x' y' : N)
  (rx : refines x x') (ry : refines y y') : refines (x < y) (x' < y')%C.
Proof. by rewrite /lt_op /lt_N N.ltb_antisym ltnNge [_ <= _]refines_boolE. Qed.


End binnat.

(* (* Some tests *) *)
(* Eval compute in 0%C. *)
(* Eval compute in (1 + 1 * 1 + 1)%C. *)