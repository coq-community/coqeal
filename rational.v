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

Import GRing.Theory.
Import Num.Theory.

(* rational - Non normalized rational numbers *)

(*************************************************************)
(* PART I: Definiting datastructures and programming with it *)
(*************************************************************)
Section Q.

Variable Z : Type.

(* Generic definition of rationals *)
Definition Q := (Z * Z)%type.

(* Definition of operators on Q Z *)
Section Q_ops.
Context `{zero Z, one Z, add Z, opp Z, mul Z, eq Z}.

(* Zero *)
Global Instance zeroQ : zero Q := (0, 1)%C.

(* One *)
Global Instance oneQ : one Q := (1, 1)%C.

(* Add *)
Global Instance addQ : add Q :=
  fun x y => (x.1 * y.2 + y.1 * x.2, x.2 * y.2)%C.

(* Mul *)
Global Instance mulQ : mul Q := 
  fun x y => (x.1 * y.1, x.2 * y.2)%C.

(* Opp *)
Global Instance oppQ : opp Q := fun x => (- x.1, x.2)%C.

(* Comp *)
Global Instance eqQ : eq Q :=
  fun x y => (x.1 * y.2 == x.2 * y.1)%C.

(* Inv *)
Global Instance invQ : inv Q :=
  fun x => (if (x.1 == 0)%C then 0%C else (x.2, x.1)%C).

(* Subtraction *)
Global Instance subQ : sub Q := fun x y => (x + - y)%C.

(* Division *)
Global Instance divQ : div Q := fun x y => (x * y^-1)%C.

(* Embedding from Z to Q *)
Global Instance embedQ : embed_class Z Q := fun x => (x, 1)%C.

End Q_ops.
End Q.

Existing Instance refines_step_refines.

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

(* We have a quotient type where rat is the quotients of Qint *)
Instance rat_refinement : refinement rat Qint :=
  Refinement Qrat_to_intK.

Lemma Qint2_eq0 (a : Qint) : (a.2 == 0) = ~~ spec a :> bool.
Proof. by rewrite /= /Qint_to_rat; case: (altP eqP). Qed.

(* this kind of things should be internalized in the theory of refinements *)
Lemma dom_refines (x : rat) (r : Qint) `{!refines x r} : r.2 != 0.
Proof. by rewrite Qint2_eq0 spec_refines. Qed.

Lemma refines_ratE (x : rat) (a : Qint) `{!refines x a} : x = a.1%:~R / a.2%:~R.
Proof. 
by apply: Some_inj; rewrite -spec_refines /= /Qint_to_rat dom_refines.
Qed.

(* We establish the correction of Q int with regard to rat *)
Instance refines_zeroq : refines_step 0 0%C. Proof. by []. Qed.
Instance refines_oneq : refines_step 1 1%C. Proof. by []. Qed.

Instance refines_embedq n : refines_step n%:~R (embedQ n).
Proof. by rewrite /refines_step /embedQ /= /Qint_to_rat /= mulr1. Qed.

Instance refines_addq (x y : rat) (a b : Qint)
         `{!refines_step x a, !refines_step y b} : refines_step (x + y) (a + b)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat mulf_neq0 ?dom_refines //=.
rewrite [x]refines_ratE [y]refines_ratE.
by rewrite addf_div ?intr_eq0 ?dom_refines ?(rmorphD, rmorphM).
Qed.

Instance refines_oppq (x : rat) (a : Qint) `{!refines_step x a} :
  refines_step (- x) (- a)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat /= ?dom_refines //=.
by rewrite [x]refines_ratE rmorphN mulNr.
Qed.

Instance refines_mulq (x y : rat) (a b : Qint)
         `{!refines_step x a, !refines_step y b} : refines_step (x * y) (a * b)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat mulf_neq0 ?dom_refines //=.
rewrite [x]refines_ratE [y]refines_ratE.
by rewrite mulrACA -invfM ?(rmorphD, rmorphM).
Qed.

Instance refines_invq (x : rat) (a : Qint) `{!refines_step x a} :
  refines_step (x^-1) (a^-1)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat /= /inv_op /invQ.
rewrite [x]refines_ratE /= -[(_ == _)%C]/(_ == _).
have [-> /=|a1_neq0 /=] := altP (a.1 =P 0); first by rewrite !mul0r ?invr0.
by rewrite a1_neq0 invfM invrK mulrC.
Qed.

Instance refines_subq (x y : rat) (a b : Qint)
 `{!refines_step x a, !refines_step y b} : refines_step (x - y) (a - b)%C.
Proof. exact/refinesP. Qed.

Instance refines_divq (x y : rat) (a b : Qint)
 `{!refines_step x a, !refines_step y b} : refines_step (x / y) (a / b)%C.
Proof. exact/refinesP. Qed.

Lemma refines_compq (x y : rat) (a b : Qint)
 `{!refines_step x a, !refines_step y b} : refines_step (x == y) (a == b)%C.
Proof.
congr Some; rewrite /= /eq_op /eqQ.
rewrite [x]refines_ratE [y]refines_ratE /= -[(_ == _)%C]/(_ == _).
rewrite divq_eq ?intr_eq0 ?dom_refines // -!rmorphM eqr_int.
by rewrite [X in (_ == X)]mulrC.
Qed.

(*************************************************************************)
(* PART III: We take advantage of parametricity to extend correcion of   *)
(* operation on Q int to correction of operations on Q Z, for any Z that *)
(* refines int                                                           *)
(*************************************************************************)
Section Qparametric.

Import parametricity.

Global Instance Qrefinement_int Z `{refinement int Z} :
  refinement rat (Q Z) :=  @refinement_trans _ Qint _ _ _.

Lemma rat_refines_trans
         Z `{refinement int Z} (x : rat) (a : Qint) (u : Q Z) :
         refines_step x a -> refines a u -> refines x u.
Proof. move=> /refines_step_refines; exact: @refines_trans. Qed.

(* Z is a type that should implement int *)
(* Variable (Z : Type). *)
Require Import ZArith binint_direct.

Local Notation Q := (Q Z).

Variables (n : int) (q : Z).
Context `{rn : !refines n q}.

Variables (x y : rat) (a b : Q).
Context `{rx : !refines x a, ry : !refines y b}.

Let u := refines_split_wit rx.
Let v := refines_split_wit ry.
Instance : refines_step x u := refines_split1 rx.
Instance : refines u a := refines_split2 rx.
Instance : refines_step y v := refines_split1 ry.
Instance : refines v b := refines_split2 ry.

Global Instance refines_zeroQ  : refines (0 : rat) (0%C : Q).
Proof. exact: rat_refines_trans. Qed.

Global Instance refines_oneQ  : refines (1 : rat) (1%C : Q).
Proof. exact: rat_refines_trans. Qed.

Global Instance refines_embedQ  : refines (n%:~R : rat) (embed q : Q).
Proof. exact: rat_refines_trans. Qed.

Global Instance refines_addQ : refines (x + y) (a + b)%C.
Proof. exact: (rat_refines_trans (refines_addq _ _ _ _)). Qed.

Global Instance refines_mulQ : refines (x * y) (a * b)%C.
Proof. exact: (rat_refines_trans (refines_mulq _ _ _ _)). Qed.

Global Instance refines_oppQ : refines (- x) (- a)%C.
Proof. exact: (rat_refines_trans (refines_oppq _ _)). Qed.

Global Instance refines_invQ : refines (x^-1) (a^-1)%C.
Proof. exact: (rat_refines_trans (refines_invq _ _)). Qed.

Global Instance refines_subQ : refines (x - y) (a - b)%C.
Proof. exact: (rat_refines_trans (refines_subq _ _ _ _)). Qed.

Global Instance refines_divQ : refines (x / y) (a / b)%C.
Proof. exact: (rat_refines_trans (refines_divq _ _ _ _)). Qed.

Global Instance refines_compQ : refines (x == y) (a == b)%C.
Proof.
assert (r1 : refines (x == y) (u == v)%C); first exact: refines_compq.
exact: (@refines_trans _ _ _ _ _ _ _ _ r1).
Qed.

End Qparametric.
End Qint.

Section tests.

Require Import ZArith binint_direct.

Lemma foo (P : bool -> Type) :
  P true -> P (1 + 1 == 1 + 1 :> rat).
Proof.
rewrite [X in _ -> P X]refines_boolE.
by vm_compute.
Qed.

End tests.
