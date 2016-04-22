(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice.
From mathcomp Require Import fintype bigop finset prime fingroup ssralg zmodp finalg.

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.

Section operations.

Global Instance zero_bool : zero_of bool := false.

Global Instance one_bool : one_of bool := true.

Global Instance opp_bool : opp_of bool := id.

Global Instance add_bool : add_of bool := xorb.

Global Instance sub_bool : sub_of bool := xorb.

Global Instance mul_bool : mul_of bool := andb.

Global Instance inv_bool : inv_of bool := id.

Global Instance eq_bool : eq_of bool := eqtype.eq_op.

End operations.

Section definition.

Local Open Scope ring_scope.
Local Open Scope rel_scope.

Definition F2_of_bool (x : bool) : 'F_2 := x%:R.

Definition Rbool := fun_hrel F2_of_bool.

Global Instance Rbool_zero : refines Rbool 0 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rbool_one : refines Rbool 1 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rbool_opp : refines (Rbool ==> Rbool) -%R -%C.
Proof.
rewrite refinesE=> x []; rewrite /Rbool /F2_of_bool /fun_hrel /= => <- //.
by rewrite GRing.mulr0n GRing.oppr0.
Qed.

Global Instance Rbool_add : refines (Rbool ==> Rbool ==> Rbool) +%R +%C.
Proof.
rewrite refinesE /Rbool /F2_of_bool /fun_hrel => x [] <- y [] <- //=.
  by rewrite -GRing.natrD char_Zp.
by rewrite GRing.add0r.
Qed.

(* TODO: lemma for sub *)
Global Instance Rbool_sub :
  refines (Rbool ==> Rbool ==> Rbool) (fun x y => x - y) sub_op.
Proof.
  rewrite refinesE /Rbool /F2_of_bool /fun_hrel=> x [] <- y [] <- //=;
  by apply/eqP; rewrite eq_sym GRing.subr_eq0.
Qed.

Global Instance Rbool_mul : refines (Rbool ==> Rbool ==> Rbool) *%R *%C.
Proof.
rewrite refinesE /Rbool /F2_of_bool /fun_hrel => x [] <- y [] <- //=.
+ by rewrite GRing.mulr0.
+ by rewrite GRing.mul0r.
by rewrite GRing.mul0r.
Qed.

Global Instance Rbool_inv : refines (Rbool ==> Rbool) GRing.inv inv_bool.
Proof.
by rewrite refinesE=> x []; rewrite /Rbool /F2_of_bool /fun_hrel /= => <- //.
Qed.

Global Instance Rbool_eq :
  refines (Rbool ==> Rbool ==> bool_R) eqtype.eq_op eq_op.
Proof.
  by rewrite refinesE /Rbool /F2_of_bool /fun_hrel=> x [] <- y [] <-.
Qed.

(*
Lemma inj_bool_trans : injective bool_of_F2.
Proof.
move=> [x Hx] [y Hy]; move: x y Hx Hy.
case; do 3?case=> //; move=> Hx Hy _; exact: val_inj.
Qed.

Definition bool_trans_struct := Trans inj_bool_trans.

Lemma bool_trans0 : bool_trans 0 = false.
Proof. by []. Qed.

Lemma oppbE : {morph bool_trans : x / - x >-> id x}.
Proof. by move=> x; rewrite /bool_trans /= GRing.oppr_eq0. Qed.

Lemma addbE : {morph bool_trans : x y / x + y >-> xorb x y}.
Proof.
move=> [x Hx] [y Hy]; move: x y Hx Hy.
case; do 3?case=> //; move=> Hx Hy _; exact: val_inj.
Qed.

(* CZmodule structure *)
Definition bool_czMixin := @CZmodMixin
  [zmodType of 'F_2] bool false
  id xorb bool_trans_struct bool_trans0 oppbE addbE.

Canonical Structure bool_czType :=
  Eval hnf in CZmodType 'F_2 bool bool_czMixin.

Lemma bool_trans1 : bool_trans 1 = true.
Proof. by []. Qed.

Lemma mulbE : {morph bool_trans : x y / x * y >-> andb x y}.
Proof.
move=> x y; rewrite /bool_trans /= GRing.mulf_eq0.
by case: (x == 0); case: (y == 0).
Qed.

Definition bool_cringMixin := CRingMixin bool_trans1 mulbE.

Canonical Structure bool_cringType :=
  Eval hnf in CRingType 'F_2 bool_cringMixin.

Lemma cunitE : (forall x : 'F_2, (x \is a GRing.unit) = xpred1 true (bool_trans x)).
Proof. by move=> x; rewrite GRing.unitfE /bool_trans eqb_id. Qed.

Lemma invbE : {morph bool_trans : x / x^-1 >-> id x}.
Proof. by do 3?case. Qed.

Definition bool_cunitRingMixin := @CUnitRingMixin [unitRingType of 'F_2]
  bool_cringType (xpred1 true) id cunitE invbE.

Canonical Structure bool_cunitRingType :=
  Eval hnf in CUnitRingType 'F_2 bool_cunitRingMixin.

*)

End definition.
