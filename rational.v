(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop ssrint ssrnum rat.
Require Import refinements pos.

(******************************************************************************)
(* Non-normalized rational numbers refinest SSReflects rational numbers (rat) *)
(*                                                                            *)
(* rational == Type of non normalized rational numbers                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Num.Theory Refinements.Op AlgOp.

(*************************************************************)
(* PART I: Defining datastructures and programming with them *)
(*************************************************************)
Section Q.

Variable Z P : Type.

(* Generic definition of rationals *)
Definition Q := (Z * P)%type.

(* Definition of operators on Q Z *)
Section Q_ops.

Local Open Scope computable_scope.

Context `{zero Z, one Z, add Z, opp Z, mul Z, eq Z, leq Z, lt Z}.
Context `{one P, sub P, add P, mul P, eq P, leq P, lt P}.
Context `{cast_class P Z, cast_class Z P}.
Context `{spec_of Z int, spec_of P pos}.

Global Instance zeroQ : zero Q := (0, 1).
Global Instance oneQ  : one Q  := (1, 1).
Global Instance addQ  : add Q  := fun x y =>
  (x.1 * cast y.2 + y.1 * cast x.2, x.2 * y.2).
Global Instance mulQ  : mul Q  := fun x y => (x.1 * y.1, x.2 * y.2).
Global Instance oppQ  : opp Q  := fun x   => (- x.1, x.2).
Global Instance eqQ   : eq Q   := fun x y => (x.1 * cast y.2 == y.1 * cast x.2).
Global Instance leqQ  : leq Q  := fun x y => (x.1 * cast y.2 <= y.1 * cast x.2).
Global Instance ltQ   : lt Q   := fun x y => (x.1 * cast y.2 < y.1 * cast x.2).
Global Instance invQ : inv Q   := fun x   =>
  if      (x.1 == 0)%C   then 0
  else if (0 < x.1)      then (cast x.2, cast x.1)
                         else (- (cast x.2), cast (- x.1)).
Global Instance subQ : sub Q   := fun x y => (x + - y).
Global Instance divQ : div Q   := fun x y => (x * y^-1).
Global Instance expQnat : exp Q nat := fun x n => iter n (mulQ x) 1.

(* Embedding from Z to Q *)
Global Instance cast_ZQ : cast_class Z Q := fun x => (x, 1).
Global Instance cast_PQ : cast_class P Q := fun x => cast (cast x : Z).

End Q_ops.
End Q.

(***********************************************************)
(* PART II: Proving the properties of the previous objects *)
(***********************************************************)
Section Qint.

Instance zero_int : zero int := 0%R.
Instance one_int  : one int  := 1%R.
Instance add_int  : add int  := +%R.
Instance opp_int  : opp int  := -%R.
Instance mul_int  : mul int  := *%R.
Instance eq_int   : eq int   := eqtype.eq_op.
Instance leq_int  : leq int  := Num.le.
Instance lt_int   : lt int   := Num.lt.

Instance one_pos : one pos := posS 0.
Instance add_pos : add pos := fun m n => insubd (posS 0) (val m + val n)%N.
Instance sub_pos : sub pos := fun m n => insubd (posS 0) (val m - val n)%N.
Instance mul_pos : mul pos := fun m n => insubd (posS 0) (val m * val n)%N.
Instance leq_pos : leq pos := fun m n => (val m <= val n)%N.
Instance lt_pos  : lt pos  := fun m n => (val m < val n)%N.
Instance eq_pos  : eq pos  := eqtype.eq_op.

Instance cast_pos_int : cast_class pos int := pos_to_int.
Instance cast_int_pos : cast_class int pos := int_to_pos.

Local Notation Qint := (Q int pos).

(* rat_to_Qint = repr *) (* Qint_to_rat = \pi_rat *)
Lemma absz_denq_gt0 r : (0 < `|denq r|)%N.
Proof. by rewrite absz_gt0 denq_eq0. Qed.

Definition rat_to_Qint (r : rat) : Qint := (numq r, pos_of (absz_denq_gt0 r)).
Definition Qint_to_rat (r : Qint) : rat := (r.1%:Q / (val r.2)%:Q).

Lemma Qrat_to_intK : cancel rat_to_Qint Qint_to_rat.
Proof. by move=> x; rewrite /Qint_to_rat /= absz_denq divq_num_den. Qed.

Definition Rrat : rat -> Q int pos -> Prop := fun_hrel Qint_to_rat.

(* Lemma Qint2_eq0 (a : Qint) : (a.2 == 0) = ~~ Qint_to_rat a :> bool. *)
(* Proof. by rewrite /= /Qint_to_rat; case: (altP eqP). Qed. *)

(* this kind of things should be internalized in the theory of refinements *)
(* Lemma dom_Rrat (x : rat) (r : Qint) : param Rrat x r -> r.2 != 0. *)
(* Proof. by rewrite paramE => rxr; rewrite Qint2_eq0 negbK rxr. Qed. *)

Lemma RratE (x : rat) (a : Qint) : param Rrat x a -> x = a.1%:~R / (val a.2)%:~R.
Proof. by rewrite paramE => <-. Qed.

(* We establish the correction of Q int with regard to rat *)
Instance Rrat_0 : param Rrat 0 0%C.
Proof. by rewrite paramE. Qed.

Instance Rrat_1 : param Rrat 1 1%C.
Proof. by rewrite paramE. Qed.

Instance Rrat_embed : param (Logic.eq ==> Rrat) intr cast.
Proof.
rewrite paramE => n _ <-.
by rewrite /Rrat /Qint_to_rat /fun_hrel /= mulr1.
Qed.

Definition pos_to_rat (x : pos) : rat := (val x)%:R.
Instance Rrat_embed_pos : param (Logic.eq ==> Rrat) pos_to_rat cast.
Proof.
rewrite paramE => n _ <-.
rewrite /Rrat /Qint_to_rat /fun_hrel /pos_to_rat /= mulr1.
by rewrite /cast /cast_pos_int /pos_to_int natz.
Qed.

Instance Rrat_add : param (Rrat ==> Rrat ==> Rrat) +%R +%C.
Proof.
apply param_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite paramE /Rrat /fun_hrel /Qint_to_rat /= /cast /cast_pos_int /=.
rewrite /pos_to_int /mul_op /mul_pos /mul_int /add_op /add_int /=.
rewrite val_insubd muln_gt0 da_gt0 db_gt0 /=.
rewrite [x]RratE [y]RratE /= addf_div ?intr_eq0 -?lt0n //.
by rewrite ?dom_Rrat ?(rmorphD, rmorphM) //= PoszM intrM !natz.
Qed.

Instance Rrat_opp : param (Rrat ==> Rrat) -%R -%C.
Proof.
apply param_abstr => x a rx; rewrite paramE /Rrat /fun_hrel /Qint_to_rat /=.
by rewrite /opp_op /opp_int [x]RratE -mulNr rmorphN.
Qed.

Instance Rrat_mul : param (Rrat ==> Rrat ==> Rrat) *%R *%C.
Proof.
apply param_abstr2  => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite paramE /Rrat /fun_hrel /Qint_to_rat /= /mul_op /mul_int /mul_pos /=.
rewrite val_insubd muln_gt0 da_gt0 db_gt0 /=.
rewrite [x]RratE [y]RratE mulrACA -invfM ?(rmorphD, rmorphM) /=.
by rewrite PoszM rmorphM /=.
Qed.

Instance Rrat_expnat : param (Rrat ==> Logic.eq ==> Rrat) (@GRing.exp _) exp_op.
Proof.
apply param_abstr2  => x a rx y n; rewrite !paramE => -> {y}.
by elim: n => //= n ihn; rewrite exprS [x * x ^+ n]RratE.
Qed.

Instance Rrat_inv : param (Rrat ==> Rrat) GRing.inv inv_op.
Proof.
apply param_abstr => x [na [da da_gt0]] /= rx.
rewrite paramE /Rrat /fun_hrel /Qint_to_rat /= /inv_op /invQ /=.
rewrite [x]RratE /= -[(_ == _)%C]/(_ == _) -[(_ < _)%C]/(_ < _) /cast.
rewrite /cast_pos_int /cast_int_pos /pos_to_int /int_to_pos /int_to_nat /=.
have [-> /=|na_neq0 /=] := altP (na =P 0).
  by rewrite !mul0r ?invr0.
have [na_gt0|na_le0] /= := ltrP 0 na.
  rewrite val_insubd absz_gt0 na_neq0 abszE ger0_norm ?ltrW //.
  by rewrite invfM invrK natz mulrC.
rewrite val_insubd /= /opp_op /opp_int /=.
rewrite oppr_gt0 ltr_neqAle na_neq0 na_le0 /= absz_gt0 oppr_eq0 na_neq0.
rewrite abszN mulrNz mulNr -mulrN -invrN -rmorphN /=.
by rewrite lez0_abs // opprK invfM invrK mulrC natz.
Qed.

Instance Rrat_eq : param (Rrat ==> Rrat ==> Logic.eq) eqtype.eq_op eq_op.
Proof.
apply param_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite paramE /eq_op /eqQ /cast /cast_pos_int /pos_to_int /=; simpC.
rewrite [x]RratE [y]RratE /= divq_eq; last 2 first.
- by rewrite gtr_eqF // ltr0z.
- by rewrite gtr_eqF // ltr0z.
by rewrite -!rmorphM /= eqr_int !natz.
Qed.

Instance Rrat_leq : param (Rrat ==> Rrat ==> Logic.eq) Num.le leq_op.
Proof.
apply param_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite paramE /leq_op /leqQ /cast /cast_pos_int /pos_to_int /=; simpC.
rewrite [x]RratE [y]RratE /= !natz.
rewrite ler_pdivr_mulr ?ltr0z // mulrAC ler_pdivl_mulr ?ltr0z //.
by rewrite -!rmorphM /= ler_int.
Qed.

Instance Rrat_lt : param (Rrat ==> Rrat ==> Logic.eq) Num.lt lt_op.
Proof.
apply param_abstr2 => x [na [da da_gt0]] rx y [nb [db db_gt0]] ry.
rewrite paramE /leq_op /leqQ /cast /cast_pos_int /pos_to_int /=; simpC.
rewrite [x]RratE [y]RratE /= !natz.
rewrite ltr_pdivr_mulr ?ltr0z // mulrAC ltr_pdivl_mulr ?ltr0z //.
by rewrite -!rmorphM /= ltr_int.
Qed.

(*************************************************************************)
(* PART III: We take advantage of parametricity to extend correcion of   *)
(* operation on Q int to correction of operations on Q Z, for any Z that *)
(* refines int                                                           *)
(*************************************************************************)
Section Qparametric.

(* Global Instance Qrefinement_int Z `{refinement int Z} : *)
(*   refinement rat (Q Z) :=  @refinement_trans _ Qint _ _ _. *)

(* (* Z is a type that should implement int *) *)
Context (Z P : Type).
Context (Rint : int -> Z -> Prop) (Rpos : pos -> P -> Prop).

Local Notation Q := (Q Z P).

Definition RratA : rat -> Q -> Prop := (Rrat \o Rint * Rpos)%rel.

(* Require Import binnat binint. *)


Context `{zero Z, one Z, add Z, opp Z, sub Z, mul Z, eq Z, leq Z, lt Z}.
Context `{one P, sub P, add P, mul P, eq P, leq P, lt P}.
Context `{cast_class P Z, cast_class Z P}.
Context `{spec_of Z int, spec_of P pos}.

Context `{!param Rint 0%R 0%C, !param Rint 1%R 1%C}.
Context `{!param (Rint ==> Rint) -%R -%C}.
Context `{!param (Rint ==> Rint ==> Rint) +%R +%C}.
Context `{!param (Rint ==> Rint ==> Rint) subr sub_op}.
Context `{!param (Rint ==> Rint ==> Rint) *%R *%C}.
Context `{!param (Rint ==> Rint ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{!param (Rint ==> Rint ==> Logic.eq) Num.le leq_op}.
Context `{!param (Rint ==> Rint ==> Logic.eq) Num.lt lt_op}.
Context `{!param (Rpos ==> Rint) cast cast}.
Context `{!param (Rint ==> Rpos) cast cast}.

Context `{!param Rpos one_pos 1%C}.
Context `{!param (Rpos ==> Rpos ==> Rpos) add_pos +%C}.
Context `{!param (Rpos ==> Rpos ==> Rpos) mul_pos *%C}.
Context `{!param (Rpos ==> Rpos ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{!param (Rpos ==> Rpos ==> Logic.eq) leq_pos leq_op}.
Context `{!param (Rpos ==> Rpos ==> Logic.eq) lt_pos lt_op}.

Global Instance RratA_zeroQ : param RratA 0 0%C.
Proof. exact: param_trans. Qed.

Global Instance RratA_oneQ  : param RratA 1 1%C.
Proof. exact: param_trans. Qed.

Global Instance RratA_cast_ZQ : param (Rint ==> RratA) intr cast.
Proof. exact: param_trans. Qed.

Global Instance RratA_cast_PQ : param (Rpos ==> RratA) pos_to_rat cast.
Proof. exact: param_trans. Qed.

Global Instance RratA_addQ : param (RratA ==> RratA ==> RratA) +%R +%C.
Proof. exact: param_trans. Qed.

Global Instance RratA_mulQ : param (RratA ==> RratA ==> RratA) *%R *%C.
Proof. exact: param_trans. Qed.

Global Instance RratA_expQnat :
  param (RratA ==> Logic.eq ==> RratA) (@GRing.exp _) exp_op.
Proof. exact: param_trans. Qed.

Global Instance RratA_oppQ : param (RratA ==> RratA) -%R -%C.
Proof. exact: param_trans. Qed.

Global Instance RratA_invQ : param (RratA ==> RratA) GRing.inv inv_op.
Proof. exact: param_trans. Qed.

Global Instance RratA_subQ : param (RratA ==> RratA ==> RratA) subr sub_op.
Proof. by rewrite /AlgOp.subr /sub_op /subQ; apply: get_param. Qed.

Global Instance RratA_divq : param (RratA ==> RratA ==> RratA) divr div_op.
Proof. by rewrite /AlgOp.divr /div_op /divQ; apply: get_param. Qed.

Global Instance RratA_eqQ : param (RratA ==> RratA ==> Logic.eq) eqtype.eq_op eq_op.
Proof.
eapply param_trans; tc.
by rewrite /eq_op /eqQ; tc.
(* temporary solution *)
Qed.

Global Instance RratA_leqQ : param (RratA ==> RratA ==> Logic.eq) Num.le leq_op.
Proof.
eapply param_trans; tc.
by rewrite /leq_op /leqQ; tc.
(* temporary solution *)
Qed.

Global Instance RratA_ltQ : param (RratA ==> RratA ==> Logic.eq) Num.lt lt_op.

Proof.
eapply param_trans; tc.
by rewrite /lt_op /ltQ; tc.
(* temporary solution *)
Qed.

End Qparametric.
End Qint.

(* Section tests. *)

(* Require Import binnat binint. *)

(* Lemma foo (P : bool -> Type) : *)
(*   P true -> *)
(*   P ((11*100+1)%N%:~R / (44*100)%N%:~R + (22*100-1)%N%:~R/(44*100)%N%:~R *)
(*      == 3%:~R / 4%:~R :> rat). *)
(* Proof. *)
(* Time by vm_compute. (* 20s *) *)
(* Restart. *)
(* Time by rewrite [X in _ -> P X]refines_boolE. (* 1s *) *)
(* (* TODO : deal with tons of successors => *)
(*    only possible through a plugin imo -- Cyril*) *)
(* Qed. *)

(* End tests. *)
