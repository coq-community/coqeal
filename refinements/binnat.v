(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ZArith Lia.

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

#[export] Instance spec_positive   : spec_of positive pos := pos_of_positive.
#[export] Instance implem_positive : implem_of pos positive := positive_of_pos.
#[export] Instance one_positive    : one_of positive := xH.
#[export] Instance add_positive    : add_of positive := Pos.add.
#[export] Instance sub_positive    : sub_of positive := Pos.sub.
#[export] Instance mul_positive    : mul_of positive := Pos.mul.
#[export] Instance le_positive     : leq_of positive := Pos.leb.
#[export] Instance lt_positive     : lt_of positive  := Pos.ltb.
#[export] Instance eq_positive     : eq_of positive  := Pos.eqb.
#[export] Instance exp_positive    : exp_of positive positive := Pos.pow.
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
by elim=> //= p <-;
rewrite ?Pos2Nat.inj_xI ?Pos2Nat.inj_xO NatTrec.trecE -mul2n.
Qed.

Lemma to_nat_gt0 p : 0 < Pos.to_nat p.
Proof.
by rewrite to_natE; elim: p => //= p; rewrite NatTrec.trecE double_gt0.
Qed.
Hint Resolve to_nat_gt0 : core.

Lemma pos_of_positiveK : cancel pos_of_positive positive_of_pos.
Proof.
move=> n /=; rewrite /positive_of_pos /pos_of_positive /=.
by rewrite val_insubd to_nat_gt0 Pos2Nat.id.
Qed.

Definition Rpos := fun_hrel pos_of_positive.

Lemma RposE (p : pos) (x : positive) :
  refines Rpos p x -> p = pos_of_positive x.
Proof. by rewrite refinesE. Qed.

Lemma RposI (p : pos) (x : positive) :
  refines Rpos p x -> x = positive_of_pos p.
Proof. by move=> /RposE ->; rewrite pos_of_positiveK. Qed.

#[export] Instance Rpos_spec_pos_r x : refines Rpos (spec x) x.
Proof. by rewrite !refinesE. Qed.

(* #[export] Instance Rpos_spec_pos_l : refines (Rpos ==> pos_R) spec_id spec. *)
(* Proof. *)
(*   rewrite refinesE=> x x'. *)
(*   rewrite -[Rpos]refinesE=> rx. *)
(*   rewrite [spec _]RposE [y in pos_of_positive y]RposI positive_of_posK /spec_id. *)
(*   exact: pos_Rxx. *)
(* Qed. *)

#[export] Instance Rpos_spec : refines (Rpos ==> Logic.eq) spec_id spec.
Proof. by rewrite refinesE. Qed.

#[export] Instance Rpos_implem : refines (Logic.eq ==> Rpos) implem_id implem.
Proof.
  rewrite refinesE=> _ x ->.
  case: x=> n ngt0.
  by rewrite /Rpos /fun_hrel positive_of_posK.
Qed.

#[export] Instance Rpos_1 : refines Rpos (pos1 : pos) (1%C : positive).
Proof. by rewrite !refinesE; apply: val_inj; rewrite /= insubdK. Qed.

#[export] Instance Rpos_add : refines (Rpos ==> Rpos ==> Rpos) add_pos +%C.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_add.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

#[export] Instance Rpos_mul : refines (Rpos ==> Rpos ==> Rpos) mul_pos *%C.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj.
rewrite !val_insubd Pos2Nat.inj_mul.
by move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
Qed.

#[export] Instance Rpos_sub : refines (Rpos ==> Rpos ==> Rpos) sub_pos sub_op.
Proof.
rewrite refinesE => _ x <- _ y <-; apply: val_inj; rewrite !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
have [/leP h|/leP h] := (ltnP (Pos.to_nat y) (Pos.to_nat x)).
  by have := (Pos2Nat.inj_sub x y); rewrite Pos2Nat.inj_lt => ->.
rewrite /sub_op /sub_positive Pos.sub_le ?Pos2Nat.inj_le //.
by rewrite subn_gt0 !ltnNge; move/leP: h ->.
Qed.

#[export] Instance Rpos_leq : refines (Rpos ==> Rpos ==> bool_R) leq_pos leq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-;
  rewrite /leq_op /le_positive /leq_pos !val_insubd.
  move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
  by case: (Pos.leb_spec0 _ _); move /Pos2Nat.inj_le /leP;
  [move ->|rewrite -eqbF_neg; move/eqP ->].
Qed.

#[export] Instance Rpos_lt : refines (Rpos ==> Rpos ==> bool_R) lt_pos lt_op.
Proof.
rewrite refinesE => /= _ x <- _ y <-; rewrite /lt_pos !val_insubd.
move: (Pos2Nat.is_pos x) (Pos2Nat.is_pos y) => /leP -> /leP ->.
have -> : (Pos.to_nat x < Pos.to_nat y) = (x < y)%C.
  by apply/ltP/idP => [|h]; rewrite -Pos2Nat.inj_lt -Pos.ltb_lt.
exact: bool_Rxx.
Qed.

#[export] Instance Rpos_eq : refines (Rpos ==> Rpos ==> bool_R) eq_pos eq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-; rewrite /eq_op /eq_positive /eq_pos.
  case: (Pos.eqb_spec _ _)=> [->|h].
    by rewrite eqxx.
  suff H : (pos_of_positive x == pos_of_positive y) = false.
    by rewrite H.
  by apply/negP=> [/eqP /(can_inj pos_of_positiveK)].
Qed.

Lemma pos2nat_inj_exp x y : Pos.to_nat (x ^ y) = Pos.to_nat x ^ Pos.to_nat y.
Proof.
  have pos2nat_pow_xO a b
       (hab : Pos.to_nat (a ^ b) = Pos.to_nat a ^ Pos.to_nat b) :
    Pos.to_nat (a ^ b~0) = (Pos.to_nat a ^ Pos.to_nat b) ^ 2.
    by rewrite -Z2Nat.inj_pos Pos2Z.inj_pow Pos2Z.inj_xO Z.mul_comm Z.pow_mul_r
               // Z.pow_2_r -Pos2Z.inj_pow Z2Nat.inj_mul // Z2Nat.inj_pos multE
               hab mulnn.
  elim: y=> [y ihy|y ihy|].
      by rewrite Pos2Nat.inj_xI multE expnS [in _ ^ _]mulnC expnM Pos.xI_succ_xO
                 Pos.pow_succ_r Pos2Nat.inj_mul multE pos2nat_pow_xO.
    by rewrite Pos2Nat.inj_xO multE mulnC expnM pos2nat_pow_xO.
  by rewrite Pos2Nat.inj_1 expn1 Pos.pow_1_r.
Qed.

#[export] Instance Rpos_exp : refines (Rpos ==> Rpos ==> Rpos) exp_pos exp_op.
Proof.
  rewrite refinesE /exp_op /exp_positive=> _ x <- _ y <-.
  apply: val_inj.
  by rewrite !val_insubd expn_gt0 !to_nat_gt0 pos2nat_inj_exp.
Qed.

End positive_theory.

#[export] Typeclasses Opaque pos_of_positive positive_of_pos.
#[global] Opaque pos_of_positive positive_of_pos.

Section binnat_op.

#[export] Instance zero_N : zero_of N := N.zero.
#[export] Instance one_N  : one_of N  := N.one.
#[export] Instance add_N  : add_of N  := N.add.

Definition succN (n : N) : N := (1 + n)%C.

#[export] Instance sub_N  : sub_of N := N.sub.
#[export] Instance exp_N  : exp_of N N := N.pow.
#[export] Instance mul_N  : mul_of N := N.mul.
#[export] Instance div_N  : div_of N := N.div.
#[export] Instance mod_N  : mod_of N := N.modulo.
#[export] Instance eq_N   : eq_of N  := N.eqb.
#[export] Instance leq_N  : leq_of N := N.leb.
#[export] Instance lt_N   : lt_of N  := N.ltb.

#[export] Instance cast_positive_N : cast_of positive N := Npos.
#[export] Instance cast_N_positive : cast_of N positive :=
  fun n => if n is Npos p then p else 1%C.

#[export] Instance spec_N : spec_of N nat := nat_of_bin.
#[export] Instance implem_N : implem_of nat N := bin_of_nat.

End binnat_op.

Section binnat_theory.

Local Open Scope rel_scope.

Definition Rnat : nat -> N -> Type := fun_hrel nat_of_bin.

Lemma RnatE (n : nat) (x : N) : refines Rnat n x -> n = x.
Proof. by rewrite refinesE. Qed.

#[export] Instance Rnat_spec_r x : refines Rnat (spec x) x.
Proof. by rewrite refinesE. Qed.

#[export] Instance Rnat_spec_l : refines (Rnat ==> nat_R) spec_id spec.
Proof.
  rewrite refinesE=> x x' rx.
  rewrite [spec _]RnatE /spec_id [y in nat_R y _]RnatE.
  exact: nat_Rxx.
Qed.

#[export] Instance Rnat_spec : refines (Rnat ==> Logic.eq) spec_id spec.
Proof. by rewrite refinesE. Qed.

#[export] Instance Rnat_implem : refines (Logic.eq ==> Rnat) implem_id implem.
Proof.
rewrite !refinesE => x _ <-.
by rewrite /Rnat /fun_hrel /implem /implem_N bin_of_natK.
Qed.

#[export] Instance Rnat_0 : refines Rnat 0 0%C.
Proof. by rewrite refinesE. Qed.

#[export] Instance Rnat_1 : refines Rnat 1%nat 1%C.
Proof. by rewrite refinesE. Qed.

Lemma nat_of_add_bin b1 b2 : (b1 + b2)%num = b1 + b2 :> nat.
Proof. by case: b1 b2 => [|p] [|q]; rewrite ?addn0 //= nat_of_add_pos. Qed.

#[export] Instance Rnat_add : refines (Rnat ==> Rnat ==> Rnat) addn +%C.
Proof.
by rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel nat_of_add_bin.
Qed.

#[export] Instance Rnat_S : refines (Rnat ==> Rnat) S succN.
Proof.
by rewrite !refinesE => m n rmn; rewrite -add1n /succN; apply: refinesP.
Qed.

Lemma nat_of_binK : forall x, N.of_nat (nat_of_bin x) = x.
Proof.
by case => //= p; apply: Nnat.N2Nat.inj; rewrite Nnat.Nat2N.id /= to_natE.
Qed.

#[export] Instance Rnat_sub : refines (Rnat ==> Rnat ==> Rnat) subn sub_op.
Proof.
rewrite refinesE => _ x <- _ y <-.
by apply: Nnat.Nat2N.inj; rewrite Nnat.Nat2N.inj_sub !nat_of_binK.
Qed.

Lemma nat_of_mul_bin b1 b2 : (b1 * b2)%num = b1 * b2 :> nat.
Proof. by case: b1 b2 => [|p] [|q]; rewrite ?muln0 //= nat_of_mul_pos. Qed.

#[export] Instance Rnat_mul : refines (Rnat ==> Rnat ==> Rnat) muln mul_op.
Proof.
rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=.
by rewrite nat_of_mul_bin.
Qed.

#[export] Instance Rnat_div_eucl :
  refines (Rnat ==> Rnat ==> prod_R Rnat Rnat) edivn N.div_eucl.
Proof.
  rewrite refinesE /Rnat /fun_hrel=> _ x <- _ y <-.
  rewrite edivn_def /=.
  case: x=> [|x] /=; first by rewrite div0n mod0n.
  case: y=> [|y] //=.
  have hspec := N.pos_div_eucl_spec x (N.pos y).
  have hrem := N.pos_div_eucl_remainder x (N.pos y).
  destruct N.pos_div_eucl.
  rewrite -[nat_of_pos _]/(nat_of_bin (N.pos _)) hspec /= {hspec}.
  rewrite nat_of_add_bin nat_of_mul_bin.
  have rem_lt_div : (n0 < N.pos y)%N.
    have pos_ne0 : N.pos y <> 0%num by [].
    have /= := hrem pos_ne0.
    rewrite /N.lt Nnat.N2Nat.inj_compare /= to_natE.
    move/nat_compare_lt/ltP.
    case: n0 {hrem}=> //= p.
    by rewrite to_natE.
  rewrite modnMDl modn_small ?rem_lt_div // divnMDl /= -?to_natE ?to_nat_gt0 //.
  by rewrite divn_small ?addn0 // ?to_natE.
Qed.

(* chunk of proof extracted from below to avoid tc
   generating spurious universe constraints *)
Lemma Rnat_div_subproof
    x x' (rx : refines Rnat x x') y y' (ry : refines Rnat y y') :
  refines (prod_R Rnat Rnat) (edivn x y) (N.div_eucl x' y').
Proof. tc. Qed.

#[export] Instance Rnat_div : refines (Rnat ==> Rnat ==> Rnat) divn div_op.
Proof.
apply refines_abstr2; rewrite /divn /div_op /div_N /N.div=> x x' rx y y' ry.
exact: (refines_apply (refines_fst_R _ _) (Rnat_div_subproof _ _)).
Qed.

#[export] Instance Rnat_mod : refines (Rnat ==> Rnat ==> Rnat) modn mod_op.
Proof.
apply refines_abstr2; rewrite /mod_op /mod_N /N.modulo=> x x' rx y y' ry.
rewrite modn_def.
exact: (refines_apply (refines_snd_R _ _) (Rnat_div_subproof _ _)).
Qed.

#[export] Instance Rnat_exp : refines (Rnat ==> Rnat ==> Rnat) expn exp_op.
Proof.
  rewrite refinesE => _ x <- _ y <-; rewrite /Rnat /fun_hrel /=.
  rewrite /exp_op /exp_N /N.pow.
  case: x y => [|x] [|y] //.
    rewrite exp0n //=; elim: y => //= p.
    by rewrite natTrecE double_gt0.
  have nat_of_binposE p : nat_of_bin (N.pos p) = Pos.to_nat p.
    elim: p=> [p ihp|p ihp|] /=; last (by rewrite Pos2Nat.inj_1);
      by rewrite ?(Pos2Nat.inj_xI, Pos2Nat.inj_xO) multE NatTrec.doubleE to_natE
                 mul2n.
  by rewrite !nat_of_binposE pos2nat_inj_exp.
Qed.

#[export] Instance Rnat_eq : refines (Rnat ==> Rnat ==> bool_R) eqtype.eq_op eq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-; rewrite /eq_op /eq_N.
  case: (N.eqb_spec _ _) => [->|/eqP hneq].
    by rewrite eqxx.
  suff H : (nat_of_bin x == nat_of_bin y) = false.
    by rewrite H.
  by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

#[export] Instance Rnat_leq : refines (Rnat ==> Rnat ==> bool_R) ssrnat.leq leq_op.
Proof.
  rewrite refinesE=> _ x <- _ y <-; rewrite /leq_op /leq_N /leq.
  case: (N.leb_spec0 _ _)=> [/N.sub_0_le|]=> h.
    by rewrite [x - y]RnatE [(_ - _)%C]h /= eqxx.
  suff H : (nat_of_bin x - nat_of_bin y == 0) = false.
    by rewrite H.
  apply/negP=> /eqP; rewrite [x - y]RnatE [0]RnatE.
  by move/(can_inj nat_of_binK)/N.sub_0_le.
Qed.

#[export] Instance Rnat_lt : refines (Rnat ==> Rnat ==> bool_R) ltn lt_op.
Proof.
apply refines_abstr2 => x x' rx y y' ry; rewrite refinesE /Rnat /fun_hrel.
rewrite /lt_op /lt_N N.ltb_antisym /ltn /= ltnNge [(y <= x)%N]refines_eq.
exact: bool_Rxx.
(* Cyril: this was wrong to do it like that, we should come back and fix *)
Qed.

#[export] Instance Rnat_cast_positive_N :
  refines (Rpos ==> Rnat) val (cast : positive -> N).
Proof.
  rewrite refinesE /cast /Rnat /fun_hrel => x x' rx.
  by rewrite [x]RposE val_insubd to_nat_gt0 to_natE.
Qed.

#[export] Instance Rnat_cast_N_positive :
  refines (Rnat ==> Rpos) (insubd pos1) (cast : N -> positive).
Proof.
  rewrite refinesE=> x x' rx; rewrite [x]RnatE.
  case: x' {x rx} => [|p] /=; last by rewrite -to_natE.
  rewrite /insubd insubF //= /cast; apply refinesP.
  apply Rpos_1.
Qed.

Lemma Rnat_eqE (c d : N) : (c == d)%C = (spec_N c == spec_N d).
Proof.
symmetry; eapply refines_eq.
refines_apply.
refines_abstr.
Qed.

Lemma Rnat_ltE (c d : N) : (c < d)%C = (spec_N c < spec_N d).
Proof.
symmetry; eapply refines_eq.
change (spec_N c < spec_N d) with (rel_of_simpl ltn (spec_N c) (spec_N d)).
refines_apply1; first refines_apply1.
refines_abstr.
Qed.

Lemma Rnat_ltP x y : reflect (x < y)%num (spec_N x < spec_N y).
Proof.
by apply: (iffP idP); rewrite -Rnat_ltE /lt_op /lt_N; apply N.ltb_lt.
Qed.

Lemma Rnat_leE (c d : N) : (c <= d)%C = (spec_N c <= spec_N d)%N.
Proof.
symmetry; eapply refines_eq.
refines_apply.
refines_abstr.
Qed.

Lemma Rnat_eqxx (c : N) : (c == c)%C.
Proof. by rewrite Rnat_eqE. Qed.

Definition Rnat_E := (Rnat_eqE, Rnat_ltE, Rnat_leE).

Lemma map_spec_N_inj : injective (map spec_N).
Proof.
apply inj_map => m n Hmn.
rewrite -(nat_of_binK m) -(nat_of_binK n).
by rewrite /spec_N in Hmn; rewrite Hmn.
Qed.

Lemma Nat2Pos_xI m : ((Pos.of_nat m.+1)~1)%positive = Pos.of_nat ((m.+1).*2.+1).
Proof.
rewrite -muln2 [RHS]Nat2Pos.inj_succ // Nat2Pos.inj_mul //.
simpl (Pos.of_nat 2); lia.
Qed.

Lemma Nat2Pos_xO m : ((Pos.of_nat m.+1)~0)%positive = Pos.of_nat ((m.+1).*2).
Proof.
rewrite -muln2 Nat2Pos.inj_mul //.
simpl (Pos.of_nat 2); lia.
Qed.

Lemma pos_of_natE m n : pos_of_nat m n = Pos.of_nat (maxn 1 (m.*2.+1 - n)).
Proof.
elim: m n => [|m IHm] n; first by rewrite /= double0 (maxn_idPl (leq_subr _ _)).
simpl.
case: n => [|n]; last case: n => [|n]; last by rewrite IHm.
- rewrite subn0 IHm.
  have->: (m.*2.+1 - m = m.+1)%N.
    rewrite -addnn subSn; first by rewrite addnK.
    exact: leq_addr.
  by rewrite !(maxn_idPr _) // Nat2Pos_xI.
- rewrite subn1 IHm.
  have->: (m.*2.+1 - m = m.+1)%N.
    rewrite -addnn subSn; first by rewrite addnK.
    exact: leq_addr.
  by rewrite !(maxn_idPr _) // Nat2Pos_xO.
Qed.

Lemma bin_of_natE : bin_of_nat =1 N.of_nat.
move=> n.
by rewrite -[bin_of_nat n]nat_of_binK bin_of_natK.
Qed.

End binnat_theory.

#[export] Typeclasses Opaque nat_of_bin bin_of_nat.
#[global] Opaque nat_of_bin bin_of_nat.

Section test.

Lemma test : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. by rewrite [X in X = _]RnatE; compute; reflexivity. Qed.

Lemma test' : 10000%num * 10000%num * (99999999%num + 1) =
             10000000000000000%num.
Proof. by apply/eqP; rewrite [_ == _]refines_eq. Qed.

End test.
