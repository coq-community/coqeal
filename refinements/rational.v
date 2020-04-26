(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset bigop order.
From mathcomp Require Import ssralg ssrint ssrnum rat.

From CoqEAL Require Import hrel param refinements pos.

(******************************************************************************)
(* Non-normalized rational numbers refines SSReflects rational numbers (rat)  *)
(*                                                                            *)
(* rational == Type of non normalized rational numbers                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Order.Theory Num.Theory Refinements.Op.

(*************************************************************)
(* PART I: Defining datastructures and programming with them *)
(*************************************************************)
Section Q.

Variable Z P N : Type.

(* Generic definition of rationals *)
Definition Q := (Z * P)%type.

(* Definition of operators on Q Z *)
Section Q_ops.

Local Open Scope computable_scope.

Context `{zero_of Z, one_of Z, add_of Z, opp_of Z, mul_of Z, eq_of Z, leq_of Z,
          lt_of Z}.
Context `{one_of P, sub_of P, add_of P, mul_of P, eq_of P, leq_of P, lt_of P}.
Context `{cast_of P Z, cast_of Z P}.
Context `{spec_of Z int, spec_of P pos, spec_of N nat}.

Global Instance zeroQ : zero_of Q := (0, 1).
Global Instance oneQ  : one_of Q  := (1, 1).
Global Instance addQ  : add_of Q  := fun x y =>
  (x.1 * cast y.2 + y.1 * cast x.2, x.2 * y.2).
Global Instance mulQ  : mul_of Q  := fun x y => (x.1 * y.1, x.2 * y.2).
Global Instance oppQ  : opp_of Q  := fun x   => (- x.1, x.2).
Global Instance eqQ   : eq_of Q   :=
  fun x y => (x.1 * cast y.2 == y.1 * cast x.2).
Global Instance leqQ  : leq_of Q  :=
  fun x y => (x.1 * cast y.2 <= y.1 * cast x.2).
Global Instance ltQ   : lt_of Q   :=
  fun x y => (x.1 * cast y.2 < y.1 * cast x.2).
Global Instance invQ : inv_of Q   := fun x   =>
  if      (x.1 == 0)%C   then 0
  else if (0 < x.1)      then (cast x.2, cast x.1)
                         else (- (cast x.2), cast (- x.1)).
Global Instance subQ : sub_of Q   := fun x y => (x + - y).
Global Instance divQ : div_of Q   := fun x y => (x * y^-1).
Global Instance expQnat : exp_of Q N := fun x n => iter (spec n) (mulQ x) 1.
Global Instance specQ : spec_of Q rat :=
  fun q => (spec q.1)%:~R / (cast (spec q.2 : pos))%:R.

(* Embedding from Z to Q *)
Global Instance cast_ZQ : cast_of Z Q := fun x => (x, 1).
Global Instance cast_PQ : cast_of P Q := fun x => cast (cast x : Z).

End Q_ops.
End Q.

Parametricity zeroQ.
Parametricity oneQ.
Parametricity addQ.
Parametricity mulQ.
Parametricity oppQ.
Parametricity eqQ.
Parametricity leqQ.
Parametricity ltQ.
Parametricity invQ.
Parametricity subQ.
Parametricity divQ.
Definition expQnat' := Eval compute in expQnat.
Parametricity expQnat'.
Realizer expQnat as expQnat_R := expQnat'_R.
Parametricity cast_ZQ.
Parametricity cast_PQ.

Arguments specQ / _ _ _ _ _ : assert.

(***********************************************************)
(* PART II: Proving the properties of the previous objects *)
(***********************************************************)
Section Qint.

Instance zero_int : zero_of int     := 0%R.
Instance one_int  : one_of int      := 1%R.
Instance add_int  : add_of int      := +%R.
Instance opp_int  : opp_of int      := -%R.
Instance mul_int  : mul_of int      := *%R.
Instance eq_int   : eq_of int       := eqtype.eq_op.
Instance leq_int  : leq_of int      := Num.le.
Instance lt_int   : lt_of int       := Num.lt.
Instance spec_int : spec_of int int := spec_id.

Instance cast_pos_int : cast_of pos int := pos_to_int.
Instance cast_int_pos : cast_of int pos := int_to_pos.
Instance spec_pos     : spec_of pos pos := spec_id.

Instance spec_nat : spec_of nat nat := spec_id.

Local Notation Qint := (Q int pos).

(* rat_to_Qint = repr *) (* Qint_to_rat = \pi_rat *)
Lemma absz_denq_gt0 r : (0 < `|denq r|)%N.
Proof. by rewrite absz_gt0 denq_eq0. Qed.

Definition rat_to_Qint (r : rat) : Qint := (numq r, pos_of (absz_denq_gt0 r)).
Definition Qint_to_rat (r : Qint) : rat := (r.1%:Q / (val r.2)%:Q).

Lemma Qrat_to_intK : cancel rat_to_Qint Qint_to_rat.
Proof. by move=> x; rewrite /Qint_to_rat /= absz_denq divq_num_den. Qed.

Local Open Scope rel_scope.

Definition Rrat : rat -> Q int pos -> Type := fun_hrel Qint_to_rat.

Instance Rrat_spec : refines (Rrat ==> Logic.eq) spec_id spec.
Proof. by rewrite refinesE=> _ x <-. Qed.

Lemma RratE (x : rat) (a : Qint) :
  refines Rrat x a -> x = a.1%:~R / (val a.2)%:~R.
Proof. by move=> rxa; rewrite -[x]/(spec_id _) [spec_id _]refines_eq. Qed.

(* We establish the correction of Q int with regard to rat *)
Instance Rrat_0 : refines Rrat 0 0%C.
Proof. by rewrite refinesE. Qed.

Instance Rrat_1 : refines Rrat 1 1%C.
Proof. by rewrite refinesE. Qed.

Instance Rrat_embed : refines (Logic.eq ==> Rrat) intr cast.
Proof.
rewrite refinesE => n _ <-.
by rewrite /Rrat /Qint_to_rat /fun_hrel /= mulr1.
Qed.

Definition pos_to_rat (x : pos) : rat := (val x)%:R.
Instance Rrat_embed_pos : refines (Logic.eq ==> Rrat) pos_to_rat cast.
Proof.
rewrite refinesE => n _ <-.
rewrite /Rrat /Qint_to_rat /fun_hrel /pos_to_rat /= mulr1.
by rewrite /cast /cast_pos_int /pos_to_int natz.
Qed.

Instance Rrat_add : refines (Rrat ==> Rrat ==> Rrat) +%R +%C.
Proof.
apply refines_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite refinesE /Rrat /fun_hrel /Qint_to_rat /= /cast /cast_pos_int /=.
rewrite /pos_to_int /mul_op /mul_pos /mul_int /add_op /add_int /=.
rewrite val_insubd muln_gt0 da_gt0 db_gt0 /=.
rewrite [x]RratE [y]RratE /= addf_div ?intr_eq0 -?lt0n //.
by rewrite ?(rmorphD, rmorphM) //= PoszM intrM !natz.
Qed.

Instance Rrat_opp : refines (Rrat ==> Rrat) -%R -%C.
Proof.
apply refines_abstr => x a rx; rewrite refinesE /Rrat /fun_hrel /Qint_to_rat /=.
by rewrite /opp_op /opp_int [x]RratE -mulNr rmorphN.
Qed.

Instance Rrat_mul : refines (Rrat ==> Rrat ==> Rrat) *%R *%C.
Proof.
apply refines_abstr2  => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite refinesE /Rrat /fun_hrel /Qint_to_rat /= /mul_op /mul_int /mul_pos /=.
rewrite val_insubd muln_gt0 da_gt0 db_gt0 /=.
rewrite [x]RratE [y]RratE mulrACA -invfM ?(rmorphD, rmorphM) /=.
by rewrite PoszM rmorphM /=.
Qed.

Instance Rrat_expnat :
  refines (Rrat ==> Logic.eq ==> Rrat) (@GRing.exp _) exp_op.
Proof.
apply refines_abstr2  => x a rx y n; rewrite !refinesE => -> {y}.
by elim: n => //= n ihn; rewrite exprS [x * x ^+ n]RratE.
Qed.

Instance Rrat_inv : refines (Rrat ==> Rrat) GRing.inv inv_op.
Proof.
apply refines_abstr => x [na [da da_gt0]] /= rx.
rewrite refinesE /Rrat /fun_hrel /Qint_to_rat /= /inv_op /invQ /=.
rewrite [x]RratE /= -[(_ == _)%C]/(_ == _) -[(_ < _)%C]/(_ < _) /cast.
rewrite /cast_pos_int /cast_int_pos /pos_to_int /int_to_pos /int_to_nat /=.
have [-> /=|na_neq0 /=] := altP (na =P 0).
  by rewrite !mul0r ?invr0.
have [na_gt0|na_le0] /= := ltrP 0 na.
  rewrite val_insubd absz_gt0 na_neq0 abszE ger0_norm ?ltW//.
  by rewrite invfM invrK natz mulrC.
rewrite val_insubd /= /opp_op /opp_int /=.
rewrite oppr_gt0 lt_neqAle na_neq0 na_le0 /= absz_gt0 oppr_eq0 na_neq0.
rewrite abszN mulrNz mulNr -mulrN -invrN -rmorphN /=.
by rewrite lez0_abs // opprK invfM invrK mulrC natz.
Qed.

Instance Rrat_eq : refines (Rrat ==> Rrat ==> bool_R) eqtype.eq_op eq_op.
Proof.
apply refines_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
have -> : (x == y) = ((na, pos_of da_gt0) == (nb, pos_of db_gt0))%C.
  rewrite /eq_op /eqQ /cast /cast_pos_int /pos_to_int /=; simpC.
  rewrite [x]RratE [y]RratE /= divq_eq; last 2 first.
  - by rewrite gt_eqF // ltr0z.
  - by rewrite gt_eqF // ltr0z.
  by rewrite -!rmorphM /= eqr_int !natz.
rewrite refinesE; exact: bool_Rxx.
Qed.

Instance Rrat_leq : refines (Rrat ==> Rrat ==> bool_R) Num.le leq_op.
Proof.
apply refines_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
have -> : (x <= y)%R = ((na, pos_of da_gt0) <= (nb, pos_of db_gt0))%C.
  rewrite /leq_op /leqQ /cast /cast_pos_int /pos_to_int /=; simpC.
  rewrite [x]RratE [y]RratE /= !natz.
  rewrite ler_pdivr_mulr ?ltr0z // mulrAC ler_pdivl_mulr ?ltr0z //.
  by rewrite -!rmorphM /= ler_int.
rewrite refinesE; exact: bool_Rxx.
Qed.

Instance Rrat_lt : refines (Rrat ==> Rrat ==> bool_R) Num.lt lt_op.
Proof.
apply refines_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
have -> : (x < y) = ((na, pos_of da_gt0) < (nb, pos_of db_gt0))%C.
  rewrite /leq_op /leqQ /cast /cast_pos_int /pos_to_int /=.
  rewrite [x]RratE [y]RratE /= /lt_op /ltQ /cast /= !natz.
  rewrite ltr_pdivr_mulr ?ltr0z // mulrAC ltr_pdivl_mulr ?ltr0z //.
  by rewrite -!rmorphM /= ltr_int.
rewrite refinesE; exact: bool_Rxx.
Qed.

Instance Rrat_sub : refines (Rrat ==> Rrat ==> Rrat) (fun x y => x - y) sub_op.
Proof.
apply refines_abstr2=> x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite refinesE /Rrat /fun_hrel /Qint_to_rat /= /cast /cast_pos_int.
rewrite /pos_to_int /mul_op /mul_pos /mul_int /add_op /add_int /=.
rewrite /opp_op /opp_int val_insubd muln_gt0 da_gt0 db_gt0 /=.
rewrite [x]RratE [y]RratE /= [(_ * _)%N%:~R]natrM !natz.
rewrite intrD !intrM -addf_div ?intr_eq0 -?lt0n //.
by rewrite -[in LHS]mulN1r intrM -[db%:~R in LHS]mul1r -mulf_div divr1 mulN1r.
Qed.

Instance Rrat_div : refines (Rrat ==> Rrat ==> Rrat) divq div_op.
Proof.
apply refines_abstr2=> x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
by rewrite /divq /div_op /divQ; tc.
Qed.

(*************************************************************************)
(* PART III: We take advantage of parametricity to extend correcion of   *)
(* operation on Q int to correction of operations on Q Z, for any Z that *)
(* refines int                                                           *)
(*************************************************************************)
Section Qparametric.

(* (* Z is a type that should implement int *) *)
Context (Z P N : Type).
Context (Rint : int -> Z -> Type) (Rpos : pos -> P -> Type)
        (Rnat : nat -> N -> Type).

Local Notation Q := (Q Z P).

Definition RratC : rat -> Q -> Type := (Rrat \o prod_R Rint Rpos)%rel.

Context `{zero_of Z, one_of Z, add_of Z, opp_of Z, sub_of Z, mul_of Z, eq_of Z,
          leq_of Z, lt_of Z}.
Context `{one_of P, sub_of P, add_of P, mul_of P, eq_of P, leq_of P, lt_of P}.
Context `{cast_of P Z, cast_of Z P}.
Context `{spec_of Z int, spec_of P pos, spec_of N nat}.

Context `{!refines Rint 0%R 0%C, !refines Rint 1%R 1%C}.
Context `{!refines (Rint ==> Rint) -%R -%C}.
Context `{!refines (Rint ==> Rint ==> Rint) +%R +%C}.
Context `{!refines (Rint ==> Rint ==> Rint) (fun x y => x - y) sub_op}.
Context `{!refines (Rint ==> Rint ==> Rint) *%R *%C}.
Context `{!refines (Rint ==> Rint ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (Rint ==> Rint ==> bool_R) Num.le leq_op}.
Context `{!refines (Rint ==> Rint ==> bool_R) Num.lt lt_op}.
Context `{!refines (Rpos ==> Rint) cast cast}.
Context `{!refines (Rint ==> Rpos) cast cast}.
Context `{!refines (Rint ==> Logic.eq) spec_id spec}.

Context `{!refines Rpos pos1 1%C}.
Context `{!refines (Rpos ==> Rpos ==> Rpos) add_pos +%C}.
Context `{!refines (Rpos ==> Rpos ==> Rpos) mul_pos *%C}.
Context `{!refines (Rpos ==> Rpos ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (Rpos ==> Rpos ==> bool_R) leq_pos leq_op}.
Context `{!refines (Rpos ==> Rpos ==> bool_R) lt_pos lt_op}.
Context `{!refines (Rpos ==> Logic.eq) spec_id spec}.

Context `{!refines (Rnat ==> nat_R) spec_id spec}.

Global Instance RratC_zeroQ : refines RratC 0 0%C.
Proof. param_comp zeroQ_R. Qed.

Global Instance RratC_oneQ  : refines RratC 1 1%C.
Proof. param_comp oneQ_R. Qed.

Global Instance RratC_cast_ZQ : refines (Rint ==> RratC) intr cast.
Proof. param_comp cast_ZQ_R. Qed.

Global Instance RratC_cast_PQ : refines (Rpos ==> RratC) pos_to_rat cast.
Proof. param_comp cast_PQ_R. Qed.

Global Instance RratC_addQ : refines (RratC ==> RratC ==> RratC) +%R +%C.
Proof. param_comp addQ_R. Qed.

Global Instance RratC_mulQ : refines (RratC ==> RratC ==> RratC) *%R *%C.
Proof. param_comp mulQ_R. Qed.

Global Instance RratC_expQnat :
  refines (RratC ==> Rnat ==> RratC) (@GRing.exp _) exp_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE; do ?move=> ?*.
  eapply (expQnat_R (N_R:=Rnat))=> // *;
    exact: refinesP.
Qed.

Global Instance RratC_oppQ : refines (RratC ==> RratC) -%R -%C.
Proof. param_comp oppQ_R. Qed.

Global Instance RratC_invQ : refines (RratC ==> RratC) GRing.inv inv_op.
Proof. param_comp invQ_R. Qed.

Global Instance RratC_subQ :
  refines (RratC ==> RratC ==> RratC) (fun x y => x - y) sub_op.
Proof. param_comp subQ_R. Qed.

Global Instance RratC_divq : refines (RratC ==> RratC ==> RratC) divq div_op.
Proof. param_comp divQ_R. Qed.

Global Instance RratC_eqQ :
  refines (RratC ==> RratC ==> bool_R) eqtype.eq_op eq_op.
Proof. param_comp eqQ_R. Qed.

Global Instance RratC_leqQ : refines (RratC ==> RratC ==> bool_R) Num.le leq_op.
Proof. param_comp leqQ_R. Qed.

Global Instance RratC_ltQ : refines (RratC ==> RratC ==> bool_R) Num.lt lt_op.
Proof. param_comp ltQ_R. Qed.

Global Instance RratC_spec : refines (RratC ==> Logic.eq) spec_id spec.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE -[Rint]refinesE -[Rpos]refinesE; move=> x y rxy.
  case: rxy=> i j rij p q rpq.
  by rewrite /spec /specQ /spec_int /spec_pos /= ![spec_id _]refines_eq.
Qed.

End Qparametric.
End Qint.

Require Import binnat binint.

Section tests.

Goal (0 == 0 :> rat).
by coqeal.
Abort.

Goal (1 == 1 :> rat).
by coqeal.
Abort.

Goal (3%:~R / 4%:~R == - (- (3 * 10)%:Z)%:~R / (2 * 20)%N%:~R :> rat).
by coqeal.
Abort.

Goal ((3%:~R / 4%:~R) * (20%:~R / 15%:~R) == 1 :> rat).
by coqeal.
Abort.

Goal ((1 / 2%:~R)^+3 == (1 / 2%:~R) - (3%:~R / 8%:~R) :> rat).
by coqeal.
Abort.

Goal ((1 / 10%:~R)^-1 == 10%:~R :> rat).
by coqeal.
Abort.

Goal ((1 / 15%:~R) / (2%:~R / 21%:~R) == 7%:~R / 10%:~R :> rat).
by coqeal.
Abort.

(* Lemma foo (P : bool -> Type) : *)
(*   P true -> *)
(*   P ((11*100+1)%N%:~R / (44*100)%N%:~R + (22*100-1)%N%:~R/(44*100)%N%:~R *)
(*      == 3%:~R / 4%:~R :> rat). *)
(* Proof. *)
(* Time by vm_compute. (* 20s *) *)
(* Restart. *)
(* Time by rewrite [X in _ -> P X]refines_boolE. (* 1s *) *)
(* (* TODO : deal with tons of successors => *) *)
(* (*    only possible through a plugin imo -- Cyril*) *)
(* Qed. *)

End tests.
