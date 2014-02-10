(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

Require Import hrel refinements pos.

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
Notation positive := positive.

Section positive_op.

Definition positive_of_pos (p : pos) : positive := Pos.of_nat (val p).
Definition pos_of_positive (p : positive) : pos := insubd pos1 (Pos.to_nat p).

Global Instance spec_positive : spec_of positive pos := pos_of_positive.
Global Instance one_positive  : one positive := xH.
Global Instance add_positive  : add positive := Pos.add.
Global Instance sub_positive  : sub positive := Pos.sub.
Global Instance mul_positive  : mul positive := Pos.mul.
Global Instance le_positive   : leq positive := Pos.leb.
Global Instance lt_positive   : lt positive  := Pos.ltb.
Global Instance eq_positive   : eq positive  := Pos.eqb.
Global Instance exp_positive  : exp positive positive := Pos.pow.
End positive_op.

Section positive_theory.

Lemma positive_of_posK : cancel positive_of_pos pos_of_positive.
Proof.
move=> n /=; rewrite /positive_of_pos /pos_of_positive /=.
apply: val_inj; rewrite Nat2Pos.id ?insubdK -?topredE ?valP //.
by apply/eqP; rewrite -lt0n valP.
Qed.

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

Lemma pos_of_positiveK : cancel  pos_of_positive positive_of_pos.
Proof.
move=> n /=; rewrite /positive_of_pos /pos_of_positive /=.
by rewrite val_insubd to_nat_gt0 Pos2Nat.id.
Qed.

Definition Rpos := fun_hrel pos_of_positive.

Lemma RposE (p : pos) (x : positive) : param Rpos p x -> p = pos_of_positive x.
Proof. by rewrite paramE. Qed.

Lemma RposI (p : pos) (x : positive) : param Rpos p x -> x = positive_of_pos p.
Proof. by move=> /RposE ->; rewrite pos_of_positiveK. Qed.

Global Instance Rpos_spec_pos_r x : param Rpos (spec x) x.
Proof. by rewrite !paramE. Qed.

Global Instance Rpos_spec_pos_l : param (Rpos ==> Logic.eq) spec_id spec.
Proof. by rewrite !paramE => x x' rx; rewrite [spec _]RposE. Qed.

Global Instance Rpos_1 : param Rpos (pos1 : pos) (1%C : positive).
Proof. by rewrite !paramE; apply: val_inj; rewrite /= insubdK. Qed.

Global Instance Rpos_add : param (Rpos ==> Rpos ==> Rpos) add_pos +%C.
Proof.
rewrite paramE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_add.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance Rpos_mul : param (Rpos ==> Rpos ==> Rpos) mul_pos *%C.
Proof.
rewrite paramE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_mul.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance Rpos_sub : param (Rpos ==> Rpos ==> Rpos) sub_pos sub_op.
Proof.
rewrite paramE => _ x <- _ y <-; apply: val_inj; rewrite !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
have [/leP h|/leP h] := (ltnP (Pos.to_nat y) (Pos.to_nat x)).
  by have := (Pos2Nat.inj_sub x y); rewrite Pos2Nat.inj_lt => ->.
rewrite /sub_op /sub_positive Pos.sub_le ?Pos2Nat.inj_le //.
by rewrite subn_gt0 !ltnNge; move/leP: h ->.
Qed.

Global Instance Rpos_leq : param (Rpos ==> Rpos ==> Logic.eq) leq_pos leq_op.
Proof.
rewrite paramE => /= _ x <- _ y <-; rewrite /leq_pos !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
by apply/leP/idP => [|h]; rewrite -Pos2Nat.inj_le -Pos.leb_le.
Qed.

Global Instance Rpos_lt : param (Rpos ==> Rpos ==> Logic.eq) lt_pos lt_op.
Proof.
rewrite paramE => /= _ x <- _ y <-; rewrite /lt_pos !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
by apply/ltP/idP => [|h]; rewrite -Pos2Nat.inj_lt -Pos.ltb_lt.
Qed.

Global Instance Rpos_eq : param (Rpos ==> Rpos ==> Logic.eq) eq_pos eq_op.
Proof.
rewrite paramE /eq_pos => /= _ x <- _ y <-.
rewrite /pos_of_positive /eq_op /eq_positive Pos.eqb_compare Pos2Nat.inj_compare.
have [/eqP->|/eqP h] := (boolP (Pos.to_nat x == Pos.to_nat y));
  rewrite -Pos2Nat.inj_compare -Pos.eqb_compare.
  by rewrite Pos.eqb_refl /insubd; case: insubP => //= u _ _; rewrite eqxx.
move: (h); rewrite Pos2Nat.inj_iff -Pos.eqb_neq => ->.
apply/negbTE; move/eqP: h; apply/contra_neq; rewrite !val_insubd.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

(* Global Instance Rpos_exp : param (Rpos ==> Rpos ==> Rpos) exp_pos exp_op.  *)
(* Proof. *)
(* rewrite /exp_op /exp_positive /Pos.pow /exp_pos. *)
(* apply param_abstr2 => [] [x x_gt0] a rx [y y_gt0] b ry. *)
(* rewrite paramE /= [a]RposI [b]RposI [1%positive]RposI. *)
(* Admitted. *)

End positive_theory.

Typeclasses Opaque pos_of_positive positive_of_pos.
Global Opaque pos_of_positive positive_of_pos.

Section binnat_op.

Global Instance zero_N : zero N := N.zero.
Global Instance one_N  : one N  := N.one.
Global Instance add_N  : add N  := N.add.

Definition succN (n : N) : N := (1 + n)%C.

Global Instance sub_N  : sub N := N.sub.
Global Instance exp_N  : exp N N := N.pow.
Global Instance mul_N  : mul N := N.mul.
Global Instance eq_N   : eq N  := N.eqb.
Global Instance leq_N  : leq N := N.leb.
Global Instance lt_N   : lt N  := N.ltb.

Global Instance cast_positive_N : cast_class positive N := Npos.
Global Instance cast_N_positive : cast_class N positive :=
  fun n => if n is Npos p then p else 1%C.

Global Instance spec_N : spec_of N nat := nat_of_bin.
Global Instance implem_N : implem_of nat N := bin_of_nat.

End binnat_op.

Section binnat_theory.

Definition Rnat : nat -> N -> Prop := fun_hrel nat_of_bin.

Lemma RnatE (n : nat) (x : N) : param Rnat n x -> n = x.
Proof. by rewrite paramE. Qed.

Global Instance Rnat_spec_r x : param Rnat (spec x) x.
Proof. by rewrite paramE. Qed.

Global Instance Rnat_spec_l : param (Rnat ==> Logic.eq) spec_id spec.
Proof. by rewrite !paramE => x x' rx; rewrite [spec _]RnatE. Qed.

Global Instance Rnat_implem : param (Logic.eq ==> Rnat) implem_id implem.
Proof.
rewrite !paramE => x _ <-.
by rewrite /Rnat /fun_hrel /implem /implem_N bin_of_natK.
Qed.

Global Instance Rnat_0 : param Rnat 0 0%C.
Proof. by rewrite paramE. Qed.

Global Instance Rnat_1 : param Rnat 1%nat 1%C.
Proof. by rewrite paramE. Qed.

Global Instance Rnat_add : param (Rnat ==> Rnat ==> Rnat) addn +%C.
Proof.
by rewrite paramE => _ x <- _ y <-; rewrite /Rnat /fun_hrel nat_of_add_bin.
Qed.

Global Instance Rnat_S : param (Rnat ==> Rnat) S succN.
Proof. by rewrite !paramE => m n rmn; rewrite -add1n /succN; apply: paramP. Qed.

Lemma nat_of_binK : forall x, N.of_nat (nat_of_bin x) = x.
Proof.
by case => //= p; apply: Nnat.N2Nat.inj; rewrite Nnat.Nat2N.id /= to_natE.
Qed.

Global Instance Rnat_sub : param (Rnat ==> Rnat ==> Rnat) subn sub_op.
Proof.
rewrite paramE => _ x <- _ y <-.
by apply: Nnat.Nat2N.inj; rewrite Nnat.Nat2N.inj_sub !nat_of_binK.
Qed.

Global Instance Rnat_mul : param (Rnat ==> Rnat ==> Rnat) muln mul_op.
Proof.
rewrite paramE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=.
by rewrite nat_of_mul_bin.
Qed.

(* Global Instance Rnat_exp : param (Rnat ==> Rnat ==> Rnat) expn exp_op. *)
(* Proof. *)
(* rewrite paramE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=. *)
(* rewrite /exp_op /exp_N /N.pow. *)
(* case: x y => [|x] [|y] //. *)
(*   rewrite exp0n //=; elim: y => //= p. *)
(*   by rewrite natTrecE double_gt0. *)
(* Admitted. *)

Global Instance Rnat_eq : param (Rnat ==> Rnat ==> Logic.eq) eqtype.eq_op eq_op.
Proof.
rewrite paramE => _ x <- _ y <-; rewrite  /eq_op /eq_N.
case: (N.eqb_spec _ _) => [->|/eqP hneq]; first by rewrite eqxx.
by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

Global Instance Rnat_leq : param (Rnat ==> Rnat ==> Logic.eq) ssrnat.leq leq_op.
Proof.
rewrite paramE => x x' rx y y' ry; rewrite /leq_op /leq_N.
case: (N.leb_spec0 _ _) => [/N.sub_0_le|] /= h.
  by apply/eqP; rewrite [x - y]RnatE [(_ - _)%C]h.
apply/negP => /eqP; rewrite [x - y]RnatE [0]RnatE.
by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

Global Instance Rnat_lt : param (Rnat ==> Rnat ==> Logic.eq) ltn lt_op.
Proof.
apply param_abstr2 => x x' rx y y' ry; rewrite paramE /Rnat /fun_hrel.
by rewrite /lt_op /lt_N N.ltb_antisym /ltn /= ltnNge [y <= x]param_eq.
(* Cyril: this was wrong to do it like that, we should come back and fix *)
Qed.

Global Instance Rnat_cast_positive_N :
  param (Rpos ==> Rnat) val (cast : positive -> N).
Proof.
apply param_abstr => x x' rx; rewrite paramE /cast /Rnat /fun_hrel.
by rewrite [x]RposE val_insubd //= to_nat_gt0 to_natE.
(* wrong mix between nat_of_pos and to_nat *)
Qed.

Global Instance Rnat_cast_N_positive :
  param (Rnat ==> Rpos) (insubd pos1) (cast : N -> positive).
Proof.
apply param_abstr => x x' rx; rewrite paramE [x]RnatE.
case: x' {x rx} => [|p] /=; last by rewrite -to_natE.
by rewrite /insubd insubF //= /cast; apply: paramP.
Qed.

End binnat_theory.

Typeclasses Opaque nat_of_bin bin_of_nat.
Global Opaque nat_of_bin bin_of_nat.

Section test.
Import Refinements.

Lemma test : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. rewrite [X in X = _]RnatE; compute; reflexivity. Qed.

Lemma test' : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. by apply/eqP; rewrite [_ == _]param_eq. Qed.

End test.
