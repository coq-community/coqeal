(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements.

(******************************************************************************)
(* The binary naturals of Coq is a refinement of SSReflects naturals (ssrnat) *) 
(*                                                                            *)
(* Supported operations are: 0, 1, +, *, ==                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

Local Instance param_refines_refines A B C D (rAB : refinement A B) (R : C -> D -> Prop)
         (c : A -> C) (d : B -> D) :
  forall a b, refines a b -> param (refines ==> R)%C c d -> param R (c a) (d b) | 2.
Proof. by move=> a b rab; rewrite !paramE; apply. Qed.

(* Notation for when we export this file *)
Notation N := N.
Notation positive := positive.

(* factor this out !*)
Notation pos := {n : nat | (n > 0)%N}.
Section positive.
Definition posS (n : nat) : pos := exist _ n.+1 isT.
Local Instance pos1 : one pos := posS 0.
Local Instance add_pos : add pos := fun m n => insubd pos1 (val m + val n).
Local Instance sub_pos : sub pos := fun m n => insubd pos1 (val m - val n).
Local Instance mul_pos : mul pos := fun m n => insubd pos1 (val m * val n).
Local Instance leq_pos : leq pos := fun m n => val m <= val n.
Local Instance lt_pos : lt pos := fun m n => val m < val n.

Definition positive_of_pos (p : pos) : positive := Pos.of_nat (val p).
Definition pos_of_positive (p : positive) : pos := insubd pos1 (Pos.to_nat p).
Lemma positive_of_posK : pcancel positive_of_pos (some \o pos_of_positive).
Proof.
move=> n /=; congr Some; rewrite /positive_of_pos /pos_of_positive /=.
apply: val_inj; rewrite Nat2Pos.id ?insubdK -?topredE ?valP //.
by apply/eqP; rewrite -lt0n valP.
Qed.

Global Instance refinement_positive : refinement pos positive :=
  Refinement positive_of_posK.

Lemma refines_posE (p : pos) (x : positive) : refines p x -> p = pos_of_positive x. 
Proof. by case. Qed.

(* Constants *)
Global Instance one_positive : one positive := xH.
Global Instance refines_pos1 : param refines (pos1 : pos) (1%C : positive).
Proof. by rewrite paramE; congr some; apply: val_inj; rewrite /= insubdK. Qed.

(* Binary operations *)
Global Instance add_positive : add positive := Pos.add.
Global Instance refines_add_pos :
  param (refines ==> refines ==> refines)%C add_pos +%C. 
Proof.
rewrite paramE => x x' rx y y' ry; congr Some; apply: val_inj; rewrite !val_insubd.
rewrite [x]refines_posE [y]refines_posE.
rewrite Pos2Nat.inj_add ?ltn_addl ?valP //.
Admitted.

Global Instance mul_positive : mul positive := Pos.mul.
Global Instance refines_mul_pos :
  param (refines ==> refines ==> refines)%C mul_pos *%C. 
Proof.
rewrite paramE => x x' rx y y' ry; congr Some; apply: val_inj; rewrite !val_insubd.
rewrite [x]refines_posE [y]refines_posE.
rewrite Pos2Nat.inj_mul ?ltn_mul ?valP //.
Admitted.

Global Instance sub_positive : sub positive := Pos.sub.
Global Instance refines_sub_pos :
  param (refines ==> refines ==> refines)%C sub_pos sub_op. 
Proof.
Admitted.

Global Instance eq_positive : eq positive := Pos.eqb.
Global Instance refines_eq_pos :
  param (refines ==> refines ==> refines)%C eqtype.eq_op eq_op. 
Proof.
Admitted.

Global Instance le_positive : leq positive := Pos.leb.
Global Instance refines_le_pos :
  param (refines ==> refines ==> refines)%C leq_pos leq_op. 
Proof.
Admitted.

Global Instance lt_positive : lt positive := Pos.ltb.
Global Instance refines_lt_pos :
  param (refines ==> refines ==> refines)%C lt_pos lt_op. 
Proof.
Admitted.

End positive.

Section binnat.

Lemma N_of_natK : pcancel bin_of_nat (some \o nat_of_bin).
Proof. by move=> n /=; rewrite bin_of_natK. Qed.

Global Instance refinement_nat_N : refinement nat N := Refinement N_of_natK.

Lemma refines_natE (n : nat) (x : N) : refines n x -> n = x. 
Proof. by case. Qed.

(* Constants *)
Global Instance zero_N : zero N := N.zero.
Global Instance refines_nat_0 : param refines 0 0%C.
Proof. by rewrite paramE. Qed.

Global Instance one_N : one N := N.one.
Global Instance refines_nat_1 : param refines 1%nat 1%C.
Proof. by rewrite paramE. Qed.

(* Binary operations *)
Global Instance add_N : add N := N.add.
Global Instance refines_nat_add :
  param (refines ==> refines ==> refines)%C addn +%C. 
Proof.
rewrite paramE => x x' rx y y' ry; rewrite /refines /=.
by rewrite [x]refines_natE [y]refines_natE nat_of_add_bin.
Qed.

Definition succN (n : N) : N := unfold (1 + n)%C.
Global Instance refines_natS : param (refines ==> refines) S succN.
Proof.
apply get_param; apply Parametricity.param_abstr => m n rmn.
by rewrite -add1n paramE; exact/refinesP.
Qed.

(* TODO: Finish! *)
Global Instance sub_N : sub N := N.sub.
Global Instance refines_nat_sub :
  param (refines ==> refines ==> refines)%C subn sub_op.
Proof.
rewrite paramE => x x' rx y y' ry; rewrite /refines /=.
rewrite [x]refines_natE [y]refines_natE.
admit.
Qed.

Global Instance mul_N : mul N := N.mul.
Global Instance refines_nat_mul :
  param (refines ==> refines ==> refines)%C muln mul_op.
Proof.
rewrite paramE => x x' rx y y' ry; rewrite /refines /=.
by rewrite [x]refines_natE [y]refines_natE nat_of_mul_bin.
Qed.

(* Comparison operations *)
Global Instance eq_N : eq N := N.eqb.
Global Instance refines_nat_eq :
  param (refines ==> refines ==> refines)%C eqtype.eq_op eq_op.
Proof.
rewrite paramE => x x' rx y y' ry.
congr Some; rewrite [x]refines_natE [y]refines_natE /eq_op /eq_N.
case: (N.eqb_spec _ _) => [->|/eqP hneq]; first by rewrite eqxx.
by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

Global Instance leq_N : leq N := N.leb.
Global Instance refines_nat_leq :
  param (refines ==> refines ==> refines)%C ssrnat.leq leq_op.
Proof.
rewrite paramE => x x' rx y y' ry; congr Some; rewrite /leq_op /leq_N.
case: (N.leb_spec0 _ _) => [/N.sub_0_le|] /= h.
  by apply/eqP; rewrite [_ - _]refines_natE  [(_ - _)%C]h.
apply/negP => /eqP; rewrite [_ - _]refines_natE [0]refines_natE.
by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

Global Instance lt_N : lt N := N.ltb.
Global Instance refines_nat_lt :
  param (refines ==> refines ==> refines)%C ltn lt_op.
Proof.
rewrite paramE => x x' rx y y' ry; rewrite /refines.
by rewrite /lt_op /lt_N N.ltb_antisym /ltn /= ltnNge [y <= x]refines_boolE.
Qed.

Global Instance cast_positive_N : cast_class positive N := Npos.
Global Instance refines_cast_positive_N :
  param (refines ==> refines)%C val (cast : positive -> N).
Proof.
rewrite paramE => x x' rx /=.
congr Some; rewrite /cast //=.
Admitted.

Global Instance cast_N_positive : cast_class N positive :=
  fun n => if n is Npos p then p else 1%C.
Global Instance refines_cast_N_positive :
  param (refines ==> refines)%C (insubd pos1) (cast : N -> positive).
Proof. Admitted.

End binnat.


(* (* Some tests *) *)
(* Eval compute in 0%C. *)
(* Eval compute in (1 + 1 * 1 + 1)%C. *)