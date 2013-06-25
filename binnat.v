(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements pos.

(******************************************************************************)
(** The binary naturals of Coq is a refinement of SSReflects naturals         *) 
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

(* Notation for when we export this file *)
Notation N := N.

Section binnat.

Definition Rnat : nat -> N -> Prop := fun_hrel nat_of_bin.

Local Instance : refinement Rpos.

Lemma RnatE (n : nat) (x : N) : param Rnat n x -> n = x. 
Proof. by rewrite paramE; case. Qed.

Global Instance spec_N : spec_of N nat := nat_of_bin.
Global Instance refines_spec_nat_r x : param Rnat (spec x) x.
Proof. by rewrite paramE. Qed.
Global Instance refines_spec_nat_l : 
  param (Rnat ==> Logic.eq) spec_id spec.
Proof. by rewrite !paramE => x x' rx; rewrite [spec _]RnatE. Qed.

(* Constants *)
Global Instance zero_N : zero N := N.zero.
Global Instance refines_nat_0 : param Rnat 0 0%C.
Proof. by rewrite paramE. Qed.

Global Instance one_N : one N := N.one.
Global Instance refines_nat_1 : param Rnat 1%nat 1%C.
Proof. by rewrite paramE. Qed.

(* Binary operations *)
Global Instance add_N : add N := N.add.
Global Instance refines_nat_add :
  param (Rnat ==> Rnat ==> Rnat) addn +%C. 
Proof.
rewrite paramE => _ x <- _ y <-.
by rewrite /Rnat /fun_hrel nat_of_add_bin.
Qed.

Definition succN (n : N) : N := unfold (1 + n)%C.
Global Instance refines_natS : param (Rnat ==> Rnat) S succN.
Proof.
rewrite !paramE => m n rmn; rewrite -add1n.
by rewrite /succN /unfold; apply: paramP.
Qed.

Lemma nat_of_binK : forall x, N.of_nat (nat_of_bin x) = x.
Proof.
case => //= p; apply: Nnat.N2Nat.inj.
by rewrite Nnat.Nat2N.id /= to_natE.
Qed.

Global Instance sub_N : sub N := N.sub.
Global Instance refines_nat_sub :
  param (Rnat ==> Rnat ==> Rnat) subn sub_op.
Proof.
rewrite paramE => _ x <- _ y <-.
by apply: Nnat.Nat2N.inj; rewrite Nnat.Nat2N.inj_sub !nat_of_binK.
Qed.

Global Instance mul_N : mul N := N.mul.
Global Instance refines_nat_mul :
  param (Rnat ==> Rnat ==> Rnat) muln mul_op.
Proof.
rewrite paramE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=.
by rewrite nat_of_mul_bin.
Qed.

(* Comparison operations *)
Global Instance eq_N : eq N := N.eqb.
Global Instance refines_nat_eq :
  param (Rnat ==> Rnat ==> Logic.eq) eqtype.eq_op eq_op.
Proof.
rewrite paramE => _ x <- _ y <-; rewrite  /eq_op /eq_N.
case: (N.eqb_spec _ _) => [->|/eqP hneq]; first by rewrite eqxx.
by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

Global Instance leq_N : leq N := N.leb.
Global Instance refines_nat_leq :
  param (Rnat ==> Rnat ==> Logic.eq) ssrnat.leq leq_op.
Proof.
rewrite paramE => x x' rx y y' ry; rewrite /leq_op /leq_N.
case: (N.leb_spec0 _ _) => [/N.sub_0_le|] /= h.
  by apply/eqP; rewrite [x - y]RnatE [(_ - _)%C]h.
apply/negP => /eqP; rewrite [x - y]RnatE [0]RnatE.
by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

Global Instance lt_N : lt N := N.ltb.
Global Instance refines_nat_lt :
  param (Rnat ==> Rnat ==> Logic.eq) ltn lt_op.
Proof.
apply param_abstr2 => x x' rx y y' ry; rewrite paramE /Rnat /fun_hrel.
by rewrite /lt_op /lt_N N.ltb_antisym /ltn /= ltnNge [y <= x]RboolE.
(* Cyril: this was wrong to do it like that, we should come back and fix *)
Qed.

Global Instance cast_positive_N : cast_class positive N := Npos.
Global Instance refines_cast_positive_N :
  param (Rpos ==> Rnat) val (cast : positive -> N).
Proof.
apply param_abstr => x x' rx; rewrite paramE /cast /Rnat /fun_hrel.
by rewrite [x]RposE val_insubd //= to_nat_gt0 to_natE. 
(* wrong mix between nat_of_pos and to_nat *)
Qed.

Global Instance cast_N_positive : cast_class N positive :=
  fun n => if n is Npos p then p else 1%C.
Global Instance refines_cast_N_positive :
  param (Rnat ==> Rpos) (insubd pos1) (cast : N -> positive).
Proof. 
apply param_abstr => x x' rx; rewrite paramE [x]RnatE.
case: x' {x rx} => [|p] /=; last by rewrite -to_natE.
by rewrite /insubd insubF //= /cast; apply: paramP.
Qed.

End binnat.

Typeclasses Opaque nat_of_bin bin_of_nat.
Global Opaque nat_of_bin bin_of_nat.

Section test.
Import Refinements.

Lemma test : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. rewrite [X in X = _]RnatE; compute; reflexivity. Qed.

Lemma test' : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. by apply/eqP; rewrite [_ == _]RboolE. Qed.

End test.
