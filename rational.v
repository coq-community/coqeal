(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp. 
Require Import path choice fintype tuple finset ssralg bigop ssrint ssrnum rat.
Require Import refinements.

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

Import GRing.Theory Num.Theory Refinements.Op.

(* rational - Non normalized rational numbers *)

(*************************************************************)
(* PART I: Defining datastructures and programming with them *)
(*************************************************************)
Section Q.

Variable Z : Type.

(* Generic definition of rationals *)
Definition Q := (Z * Z)%type.

(* Definition of operators on Q Z *)
Section Q_ops.
Context `{zero Z, one Z, add Z, opp Z, mul Z, eq Z}.

(* Zero *)
Global Instance zeroQ : zero Q := unfold (0, 1)%C.

(* One *)
Global Instance oneQ : one Q := unfold (1, 1)%C.

(* Add *)
Global Instance addQ : add Q :=
  fun x y => unfold (x.1 * y.2 + y.1 * x.2, x.2 * y.2)%C.

(* Mul *)
Global Instance mulQ : mul Q := 
  fun x y => unfold (x.1 * y.1, x.2 * y.2)%C.

(* Opp *)
Global Instance oppQ : opp Q := fun x => unfold (- x.1, x.2)%C.

(* Comp *)
Global Instance eqQ : eq Q :=
  fun x y => unfold (x.1 * y.2 == x.2 * y.1)%C.

(* Inv *)
Global Instance invQ : inv Q :=
  fun x => (if (x.1 == 0)%C then 0%C else (x.2, x.1)%C).

(* Subtraction *)
Global Instance subQ : sub Q := fun x y => unfold (x + - y)%C.

(* Division *)
Global Instance divQ : div Q := fun x y => unfold (x * y^-1)%C.

(* Embedding from Z to Q *)
Global Instance embedQ : cast_class Z Q := fun x => unfold (x, 1)%C.

End Q_ops.
End Q.

(***********************************************************)
(* PART II: Proving the properties of the previous objects *)
(***********************************************************)
Section Qint.

Instance : zero int := 0%R.
Instance : one int  := 1%R.
Instance : add int  := +%R.
Instance : opp int  := -%R.
Instance : mul int  := *%R.
Instance : eq int   := eqtype.eq_op.

(* Q int refines rat *)
Local Notation Qint := (Q int).

(* rat_to_Qint = repr *) (* Qint_to_rat = \pi_rat *)
Definition rat_to_Qint (r : rat) : Qint := (numq r, denq r).
Definition Qint_to_rat (r : Qint) : option rat :=
  if r.2 != 0 then Some (r.1%:Q / r.2%:Q) else None.

Lemma Qrat_to_intK : pcancel rat_to_Qint Qint_to_rat.
Proof. by move=> x; rewrite /Qint_to_rat ?denq_eq0 ?divq_num_den. Qed.

Definition Rrat : rat -> Q int -> Prop := ofun_hrel Qint_to_rat.

Lemma Qint2_eq0 (a : Qint) : (a.2 == 0) = ~~ Qint_to_rat a :> bool.
Proof. by rewrite /= /Qint_to_rat; case: (altP eqP). Qed.

(* this kind of things should be internalized in the theory of refinements *)
Lemma dom_refines (x : rat) (r : Qint) : param Rrat x r -> r.2 != 0.
Proof. by rewrite paramE => rxr; rewrite Qint2_eq0 negbK rxr. Qed.

Lemma RratE (x : rat) (a : Qint) : param Rrat x a -> x = a.1%:~R / a.2%:~R.
Proof. 
rewrite paramE => rxa.
by apply: Some_inj; rewrite -rxa /= /Qint_to_rat dom_refines.
Qed.

(* We establish the correction of Q int with regard to rat *)
Local Instance refines_zeroq : param Rrat 0 0%C.
Proof. by rewrite paramE. Qed.
Local Instance refines_oneq : param Rrat 1 1%C.
Proof. by rewrite paramE. Qed.

Local Instance refines_embedq :
  param (Logic.eq ==> Rrat) intr (cast : int -> Q _).
Proof. 
rewrite paramE => n ? <-.
by rewrite /refines /Rrat /ofun_hrel /cast /embedQ /= /Qint_to_rat /= mulr1.
Qed.


Local Instance refines_addq :
  param (Rrat ==> Rrat ==> Rrat) +%R +%C.
Proof.
apply param_abstr2 => x a rx y b ry; rewrite paramE.
rewrite /refines /Rrat /ofun_hrel /= /Qint_to_rat mulf_neq0 ?dom_refines //=.
rewrite [x]RratE [y]RratE.
by rewrite addf_div ?intr_eq0 ?dom_refines ?(rmorphD, rmorphM).
Qed.

Local Instance refines_oppq : param (Rrat ==> Rrat) -%R -%C.
Proof.
apply param_abstr => x a rx; rewrite paramE.
rewrite /refines /Rrat /ofun_hrel /= /Qint_to_rat /= ?dom_refines //=.
by rewrite [x]RratE rmorphN mulNr.
Qed.

Local Instance refines_mulq :
  param (Rrat ==> Rrat ==> Rrat) *%R *%C.
Proof.
apply param_abstr2  => x a rx y b ry; rewrite paramE.
rewrite /refines /Rrat /ofun_hrel /= /Qint_to_rat mulf_neq0 ?dom_refines //=.
rewrite [x]RratE [y]RratE.
by rewrite mulrACA -invfM ?(rmorphD, rmorphM).
Qed.

Local Instance refines_invq :
  param (Rrat ==> Rrat) GRing.inv (@inv_op Qint _).
Proof.
apply param_abstr => x a rx; rewrite paramE.
rewrite /refines /Rrat /ofun_hrel /= /Qint_to_rat /= /inv_op /invQ.
rewrite [x]RratE /= -[(_ == _)%C]/(_ == _).
have [-> /=|a1_neq0 /=] := altP (a.1 =P 0); first by rewrite !mul0r ?invr0.
by rewrite a1_neq0 invfM invrK mulrC.
Qed.

Local Instance refines_compq :
  param (Rrat ==> Rrat ==> Logic.eq) eqtype.eq_op (@eq_op Qint _).
Proof.
apply param_abstr2  => x a rx y b ry; rewrite paramE /= /eq_op /eqQ.
rewrite [x]RratE [y]RratE /= -[(_ == _)%C]/(_ == _).
rewrite divq_eq ?intr_eq0 ?dom_refines // -!rmorphM eqr_int.
by rewrite [X in (_ == X)]mulrC.
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
Context (C : Type) (rintC : int -> C -> Prop).                                                                  

Definition RratA := (@Rrat \o prod_hrel rintC rintC)%rel.  

Require Import binnat binint. 

Local Notation Q := (Q C).

Context `{zero C, one C, opp C, add C, sub C, mul C, eq C}.

Context `{!param rintC 0%R 0%C, !param rintC 1%R 1%C}.
Context `{!param (rintC ==> rintC) -%R -%C}.
Context `{!param (rintC ==> rintC ==> rintC) +%R +%C}.
Context `{!param (rintC ==> rintC ==> rintC) subr sub_op}.
Context `{!param (rintC ==> rintC ==> rintC) *%R *%C}.
Context `{!param (rintC ==> rintC ==> Logic.eq) eqtype.eq_op eq_op}.

Local Instance param_fst A B (R : A -> B -> Prop) A' B' (R' : A' -> B' -> Prop) :
  param (R * R' ==> R) (@fst _ _) (@fst _ _).
Proof. exact: get_param. Qed.

Local Instance param_snd A B (R : A -> B -> Prop) A' B' (R' : A' -> B' -> Prop) :
  param (R * R' ==> R') (@snd _ _) (@snd _ _).
Proof. exact: get_param. Qed.

Global Instance refines_zeroQ  : param RratA (0 : rat) (0%C : Q).
Proof. exact: param_trans. Qed.

Global Instance refines_oneQ  : param RratA (1 : rat) (1%C : Q).
Proof. exact: param_trans. Qed.

Global Instance refines_embedQ :
    param (rintC ==> RratA) intr (cast: C -> Q).
Proof. exact: param_trans. Qed.

Global Instance refines_addQ :
  param (RratA ==> RratA ==> RratA) +%R (+%C : Q -> Q -> Q).
Proof. exact: param_trans. Qed.

Global Instance refines_mulQ :
  param (RratA ==> RratA ==> RratA) *%R ( *%C : Q -> Q -> Q).
Proof. exact: param_trans. Qed.

Global Instance refines_oppQ :
  param (RratA ==> RratA) -%R (-%C : Q -> Q).
Proof. exact: param_trans. Qed.

Global Instance refines_invQ :
  param (RratA ==> RratA) GRing.inv (@inv_op Q _).
Proof. exact: param_trans. Qed.

Global Instance refines_subQ :
  param (RratA ==> RratA ==> RratA) AlgOp.subr (@sub_op Q _).
Proof. by rewrite /AlgOp.subr /sub_op /subQ /unfold; apply: get_param. Qed.

Global Instance refines_divq :
  param (RratA ==> RratA ==> RratA) AlgOp.divr (@div_op Q _).
Proof. rewrite /AlgOp.divr /div_op /divQ /unfold; exact: get_param. Qed.

Global Instance refines_eqQ :
  param (RratA ==> RratA ==> Logic.eq) eqtype.eq_op (@eq_op Q _).
Proof.
eapply param_trans; tc.
by rewrite /eq_op /eqQ /unfold; tc.
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
