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
Lemma positive_of_posK : cancel positive_of_pos pos_of_positive.
Proof.
move=> n /=; rewrite /positive_of_pos /pos_of_positive /=.
apply: val_inj; rewrite Nat2Pos.id ?insubdK -?topredE ?valP //.
by apply/eqP; rewrite -lt0n valP.
Qed.

Definition Rpos := fun_hrel pos_of_positive.

Global Program Instance refinement_positive : refinement Rpos.

Lemma RposE (p : pos) (x : positive) : param Rpos p x -> p = pos_of_positive x. 
Proof. by rewrite paramE; case. Qed.

(* Why is this not in ssrnat? *)
Lemma to_natE : forall (p : positive), Pos.to_nat p = nat_of_pos p.
Proof.
by elim=> //= p <-; rewrite ?Pos2Nat.inj_xI ?Pos2Nat.inj_xO NatTrec.trecE -mul2n.
Qed.

Lemma to_nat_gt0 p : 0 < Pos.to_nat p.
Proof.
by rewrite to_natE; elim: p => //= p; rewrite NatTrec.trecE double_gt0.
Qed.
Hint Resolve to_nat_gt0.

Definition spec_id {A} : A -> A := id.
Global Instance spec_positive : spec_of positive pos := pos_of_positive.
Global Instance Rpos_spec : param (Logic.eq ==> Rpos) spec spec_id.
Proof. by rewrite !paramE; move=> x y <-. Qed.

(* Constants *)
Global Instance one_positive : one positive := xH.
Global Instance refines_pos1 : param Rpos (pos1 : pos) (1%C : positive).
Proof. by rewrite !paramE; apply: val_inj; rewrite /= insubdK. Qed.

(* Binary operations *)
Global Instance add_positive : add positive := Pos.add.
Global Instance refines_add_pos :
  param (Rpos ==> Rpos ==> Rpos) add_pos +%C. 
Proof.
rewrite paramE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_add.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance mul_positive : mul positive := Pos.mul.
Global Instance refines_mul_pos :
  param (Rpos ==> Rpos ==> Rpos) mul_pos *%C. 
Proof.
rewrite paramE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_mul.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance sub_positive : sub positive := Pos.sub.
Global Instance refines_sub_pos :
  param (Rpos ==> Rpos ==> Rpos) sub_pos sub_op. 
Proof.
rewrite paramE => _ x <- _ y <-; apply: val_inj; rewrite !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
have [/leP h|/leP h] := (ltnP (Pos.to_nat y) (Pos.to_nat x)).
  by have := (Pos2Nat.inj_sub x y); rewrite Pos2Nat.inj_lt => ->.
rewrite /sub_op /sub_positive Pos.sub_le ?Pos2Nat.inj_le //.
by rewrite subn_gt0 !ltnNge; move/leP: h ->.
Qed.

(* TODO: This proof is not nice! *)
Global Instance eq_positive : eq positive := Pos.eqb.
Global Instance refines_eq_pos :
  param (Rpos ==> Rpos ==> Logic.eq) eqtype.eq_op eq_op. 
Proof.
rewrite paramE => /= _ x <- _ y <-.
rewrite /pos_of_positive /eq_op /eq_positive Pos.eqb_compare Pos2Nat.inj_compare.
have [/eqP->|/eqP h] := (boolP (Pos.to_nat x == Pos.to_nat y)); 
  rewrite -Pos2Nat.inj_compare -Pos.eqb_compare.
  by rewrite Pos.eqb_refl /insubd; case: insubP => //= u _ _; rewrite eqxx.
move: (h); rewrite Pos2Nat.inj_iff -Pos.eqb_neq => ->.
apply/negbTE; move/eqP: h; apply/contra_neq; rewrite !val_insubd.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance le_positive : leq positive := Pos.leb.
Global Instance refines_le_pos :
  param (Rpos ==> Rpos ==> Logic.eq) leq_pos leq_op. 
Proof.
rewrite paramE => /= _ x <- _ y <-; rewrite /leq_pos !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
by apply/leP/idP => [|h]; rewrite -Pos2Nat.inj_le -Pos.leb_le.
Qed.

Global Instance lt_positive : lt positive := Pos.ltb.
Global Instance refines_lt_pos :
  param (Rpos ==> Rpos ==> Logic.eq) lt_pos lt_op. 
Proof.
rewrite paramE => /= _ x <- _ y <-; rewrite /lt_pos !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
by apply/ltP/idP => [|h]; rewrite -Pos2Nat.inj_lt -Pos.ltb_lt.
Qed.

End positive.

Section binnat.

Definition Rnat : nat -> N -> Prop := fun_hrel nat_of_bin.

Global Program Instance refinement_nat_N : refinement Rnat.

Lemma RboolE (b b' : bool) : param Logic.eq b b' -> b = b'. 
Proof. by rewrite paramE. Qed.

Lemma RnatE (n : nat) (x : N) : param Rnat n x -> n = x. 
Proof. by rewrite paramE; case. Qed.

Global Instance spec_N : spec_of N nat := nat_of_bin.
Global Instance Rnat_spec : param (Logic.eq ==> Rnat) spec spec_id.
Proof. by rewrite paramE => x _ <-. Qed.

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
