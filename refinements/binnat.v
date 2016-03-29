(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

From CoqEAL Require Import hrel param refinements pos.

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

Global Instance spec_positive   : spec_of positive pos := pos_of_positive.
Global Instance implem_positive : implem_of pos positive := positive_of_pos.
Global Instance one_positive    : one_of positive := xH.
Global Instance add_positive    : add_of positive := Pos.add.
Global Instance sub_positive    : sub_of positive := Pos.sub.
Global Instance mul_positive    : mul_of positive := Pos.mul.
Global Instance le_positive     : leq_of positive := Pos.leb.
(*Global Instance lt_positive     : lt positive  := Pos.ltb.*)
Global Instance eq_positive     : eq_of positive  := Pos.eqb.
(*Global Instance exp_positive    : exp positive positive := Pos.pow.*)
End positive_op.

Section positive_theory.

Local Open Scope rel_scope.

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

Lemma pos_of_positiveK : cancel pos_of_positive positive_of_pos.
Proof.
move=> n /=; rewrite /positive_of_pos /pos_of_positive /=.
by rewrite val_insubd to_nat_gt0 Pos2Nat.id.
Qed.

Definition Rpos := fun_hrel pos_of_positive.

Lemma RposE (p : pos) (x : positive) : refines Rpos p x -> p = pos_of_positive x.
Proof. by rewrite refinesE. Qed.

Lemma RposI (p : pos) (x : positive) : refines Rpos p x -> x = positive_of_pos p.
Proof. by move=> /RposE ->; rewrite pos_of_positiveK. Qed.

Global Instance Rpos_spec_pos_r x : refines Rpos (spec x) x.
Proof. by rewrite !refinesE. Qed.

(* Global Instance Rpos_spec_pos_l : refines (Rpos ==> pos_R) spec_id spec. *)
(* Proof. *)
(*   rewrite refinesE=> x x'. *)
(*   rewrite -[Rpos]refinesE=> rx. *)
(*   rewrite [spec _]RposE [y in pos_of_positive y]RposI positive_of_posK /spec_id. *)
(*   exact: pos_Rxx. *)
(* Qed. *)

Global Instance Rpos_spec : refines (Rpos ==> Logic.eq) spec_id spec.
Proof. by rewrite refinesE. Qed.

Global Instance Rpos_1 : refines Rpos (pos1 : pos) (1%C : positive).
Proof. by rewrite !refinesE; apply: val_inj; rewrite /= insubdK. Qed.

Global Instance Rpos_add : refines (Rpos ==> Rpos ==> Rpos) add_pos +%C.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_add.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance Rpos_mul : refines (Rpos ==> Rpos ==> Rpos) mul_pos *%C.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_mul.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

Global Instance Rpos_sub : refines (Rpos ==> Rpos ==> Rpos) sub_pos sub_op.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj; rewrite !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
have [/leP h|/leP h] := (ltnP (Pos.to_nat y) (Pos.to_nat x)).
  by have := (Pos2Nat.inj_sub x y); rewrite Pos2Nat.inj_lt => ->.
rewrite /sub_op /sub_positive Pos.sub_le ?Pos2Nat.inj_le //.
by rewrite subn_gt0 !ltnNge; move/leP: h ->.
Qed.

Global Instance Rpos_leq : refines (Rpos ==> Rpos ==> bool_R) leq_pos leq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-;
  rewrite /leq_op /le_positive /leq_pos !val_insubd.
  move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
  by case: (Pos.leb_spec0 _ _); move /Pos2Nat.inj_le /leP;
  [move ->|rewrite -eqbF_neg; move/eqP ->].
Qed.

(*Global Instance Rpos_lt : param (Rpos ==> Rpos ==> Logic.eq) lt_pos lt_op.
Proof.
rewrite paramE => /= _ x <- _ y <-; rewrite /lt_pos !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
by apply/ltP/idP => [|h]; rewrite -Pos2Nat.inj_lt -Pos.ltb_lt.
Qed.*)

Global Instance Rpos_eq : refines (Rpos ==> Rpos ==> bool_R) eq_pos eq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-; rewrite /eq_op /eq_positive /eq_pos.
  case: (Pos.eqb_spec _ _)=> [->|h].
    by rewrite eqxx.
  suff H : (pos_of_positive x == pos_of_positive y) = false.
    by rewrite H.
  by apply/negP=> [/eqP /(can_inj pos_of_positiveK)].
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

Global Instance zero_N : zero_of N := N.zero.
Global Instance one_N  : one_of N  := N.one.
Global Instance add_N  : add_of N  := N.add.

Definition succN (n : N) : N := (1 + n)%C.

Global Instance sub_N  : sub_of N := N.sub.
(*Global Instance exp_N  : exp N N := N.pow.*)
Global Instance mul_N  : mul_of N := N.mul.
Global Instance eq_N   : eq_of N  := N.eqb.
Global Instance leq_N  : leq_of N := N.leb.
(*Global Instance lt_N   : lt N  := N.ltb.*)

Global Instance cast_positive_N : cast_of positive N := Npos.
Global Instance cast_N_positive : cast_of N positive :=
  fun n => if n is Npos p then p else 1%C.

Global Instance spec_N : spec_of N nat := nat_of_bin.
Global Instance implem_N : implem_of nat N := bin_of_nat.

End binnat_op.

Section binnat_theory.

Local Open Scope rel_scope.

Definition Rnat : nat -> N -> Type := fun_hrel nat_of_bin.

Lemma RnatE (n : nat) (x : N) : refines Rnat n x -> n = x.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_spec_r x : refines Rnat (spec x) x.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_spec_l : refines (Rnat ==> nat_R) spec_id spec.
Proof.
  rewrite refinesE=> x x' rx.
  rewrite [spec _]RnatE /spec_id [y in nat_R y _]RnatE.
  exact: nat_Rxx.
Qed.

Global Instance Rnat_spec : refines (Rnat ==> Logic.eq) spec_id spec.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_implem : refines (Logic.eq ==> Rnat) implem_id implem.
Proof.
rewrite !refinesE => x _ <-.
by rewrite /Rnat /fun_hrel /implem /implem_N bin_of_natK.
Qed.

Global Instance Rnat_implem_nat : refines (nat_R ==> Rnat) implem_id implem.
Proof.
  rewrite refinesE=> x y rxy.
  rewrite (nat_R_eq rxy).
  by rewrite /Rnat /fun_hrel /implem /implem_N bin_of_natK.
Qed.

Global Instance Rnat_0 : refines Rnat 0 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_1 : refines Rnat 1%nat 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_add : refines (Rnat ==> Rnat ==> Rnat) addn +%C.
Proof.
by rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel nat_of_add_bin.
Qed.

Global Instance Rnat_S : refines (Rnat ==> Rnat) S succN.
Proof. by rewrite !refinesE => m n rmn; rewrite -add1n /succN; apply: refinesP. Qed.

Lemma nat_of_binK : forall x, N.of_nat (nat_of_bin x) = x.
Proof.
by case => //= p; apply: Nnat.N2Nat.inj; rewrite Nnat.Nat2N.id /= to_natE.
Qed.

Global Instance Rnat_sub : refines (Rnat ==> Rnat ==> Rnat) subn sub_op.
Proof.
rewrite refinesE => _ x <- _ y <-.
by apply: Nnat.Nat2N.inj; rewrite Nnat.Nat2N.inj_sub !nat_of_binK.
Qed.

Global Instance Rnat_mul : refines (Rnat ==> Rnat ==> Rnat) muln mul_op.
Proof.
rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=.
by rewrite nat_of_mul_bin.
Qed.

(* Global Instance Rnat_exp : refines (Rnat ==> Rnat ==> Rnat) expn exp_op. *)
(* Proof. *)
(* rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=. *)
(* rewrite /exp_op /exp_N /N.pow. *)
(* case: x y => [|x] [|y] //. *)
(*   rewrite exp0n //=; elim: y => //= p. *)
(*   by rewrite natTrecE double_gt0. *)
(* Admitted. *)

Global Instance Rnat_eq : refines (Rnat ==> Rnat ==> bool_R) eqtype.eq_op eq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-; rewrite /eq_op /eq_N.
  case: (N.eqb_spec _ _) => [->|/eqP hneq].
    by rewrite eqxx.
  suff H : (nat_of_bin x == nat_of_bin y) = false.
    by rewrite H.
  by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

Global Instance Rnat_leq : refines (Rnat ==> Rnat ==> bool_R) ssrnat.leq leq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-; rewrite /leq_op /leq_N /leq.
  case: (N.leb_spec0 _ _)=> [/N.sub_0_le|]=> h.
    by rewrite [x - y]RnatE [(_ - _)%C]h /= eqxx.
  suff H : (nat_of_bin x - nat_of_bin y == 0) = false.
    by rewrite H.
  apply/negP=> /eqP; rewrite [x - y]RnatE [0]RnatE.
  by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

(*Global Instance Rnat_lt : refines (Rnat ==> Rnat ==> Logic.eq) ltn lt_op.
Proof.
apply refines_abstr2 => x x' rx y y' ry; rewrite refinesE /Rnat /fun_hrel.
by rewrite /lt_op /lt_N N.ltb_antisym /ltn /= ltnNge [y <= x]refines_eq.
(* Cyril: this was wrong to do it like that, we should come back and fix *)
Qed.*)

Global Instance Rnat_cast_positive_N :
  refines (Rpos ==> Rnat) val (cast : positive -> N).
Proof.
  rewrite refinesE /cast /Rnat /fun_hrel => x x' rx.
  by rewrite [x]RposE val_insubd to_nat_gt0 to_natE.
Qed.

Global Instance Rnat_cast_N_positive :
  refines (Rnat ==> Rpos) (insubd pos1) (cast : N -> positive).
Proof.
  rewrite refinesE=> x x' rx; rewrite [x]RnatE.
  case: x' {x rx} => [|p] /=; last by rewrite -to_natE.
  rewrite /insubd insubF //= /cast; apply refinesP.
  apply Rpos_1.
Qed.

End binnat_theory.

Typeclasses Opaque nat_of_bin bin_of_nat.
Global Opaque nat_of_bin bin_of_nat.

Section test.
Import Refinements.

Lemma test : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. by rewrite [X in X = _]RnatE; compute; reflexivity. Qed.

Lemma test' : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. by apply/eqP; rewrite [_ == _]refines_eq. Qed.

End test.
