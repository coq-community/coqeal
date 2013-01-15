(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp. 
Require Import path choice fintype tuple finset ssralg bigop ssrint ssrnum rat.
Require Import generic_quotient refinements.

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
Local Open Scope quotient_scope.
Local Open Scope signature_scope.

Import GRing.Theory.
Import Num.Theory.

(* rational - Non normalized rational numbers *)
Section rational.

Record rational := Rational {
  valr     : (int * int) ;
  valr_gt0 : (0 < valr.2)
}.

Canonical rational_subType := Eval hnf in [subType for valr].

Lemma valr_inj : injective valr.
Proof. exact: val_inj. Qed.

(* denormalize = repr *) (* normalize = \pi_rat *)
Definition denormalize (r : rat) : rational := @Rational (valq r) (denq_gt0 r).
Definition normalize (r : rational) : rat := fracq (valr r).

Lemma normalizeK : cancel denormalize normalize.
Proof. by move=> x; rewrite /normalize /denormalize valqK. Qed.

(* We have a quotient type where rat is the quotients of rat' *)
Global Instance quotClass : quotient_of rational rat := QuotClass normalizeK.

(* Zero - Use repr_of to avoid lock on repr *)
Definition zero_rational : rational := @Rational (0, 1) (erefl).
Global Program Instance ZeroRational : Zero rational := zero_rational.

(* One *)
Definition one_rational : rational := @Rational (1, 1) (erefl).
Global Program Instance OneRational : One rational := one_rational.

(* Add *)
Fact add_rational_sub : forall a b, 0 < (addq_subdef (valr a) (valr b)).2.
Proof. by case => a a0 [b b0]; rewrite mulr_gt0. Qed.
Definition add_rational a b := Rational (add_rational_sub a b).
Global Program Instance AddRational : Add rational := add_rational.

(* Opp *)
Fact opp_rational_sub : forall a, 0 < (oppq_subdef (valr a)).2.
Proof. by case. Qed.
Definition opp_rational a := Rational (opp_rational_sub a).
Global Program Instance OppRational : Opp rational := opp_rational.

(* Mul *)
Fact mul_rational_sub : forall a b, 0 < (mulq_subdef (valr a) (valr b)).2.
Proof. by case => a a0 [b b0]; rewrite mulr_gt0. Qed.
Definition mul_rational a b := Rational (mul_rational_sub a b).
Global Program Instance MulRational : Mul rational := mul_rational.

(* Inv *)
Definition inv_rational_subdef (a : int * int) := 
  valq (fracq (invq_subdef a)).
Fact inv_rational_sub : forall a, 0 < (inv_rational_subdef (valr a)).2.
Proof.
case => [[a1 a2] /= h0].
have [//|a1_neq0] := altP (a1 =P 0). 
rewrite ltz_nat divn_gt0 dvdn_leq //; first by rewrite absz_gt0.
  by rewrite dvdn_gcdr.
by rewrite gcdn_gt0 !absz_gt0 a1_neq0 orbT.
Qed.
Definition inv_rational a := Rational (inv_rational_sub a).
Global Program Instance InvRational : Inv rational := inv_rational.

(* Subtraction *)
Definition sub_rational (a b : rational) := (a + - b)%C.
Global Program Instance SubRational : Sub rational := sub_rational.

(* Division *)
Definition div_rational (a b : rational) := (a * b^-1)%C.
Global Program Instance DivRational : Div rational := div_rational.

(* Global Program Instance ZeroMorphRational : implem_of (0 : rat) 0%C. *)
(* Obligation 1. by rewrite /implem /quot_implem unlock. Qed. *)

(* (* One - Use repr_of to avoid lock on repr *) *)
(* Global Program Instance OneMorphRational : implem_of (1 : rat) 1%C. *)
(* Obligation 1. by rewrite /implem /quot_implem unlock. Qed. *)

(* Addition *)

(* Adding and then normalizing should be the same as first normalizing and
   then adding *)
Lemma add_rationalE : {morph \pi_rat%C : a b / (a + b)%C >-> a + b }.
Proof.
rewrite /= /normalize /valr => [[[a1 a2]] /= h1 [[b1 b2]] /= h2].
have ha2_neq0 : a2 != 0 by apply/negP => h0; move: h1; rewrite (eqP h0).
have hb2_neq0 : b2 != 0 by apply/negP => h0; move: h2; rewrite (eqP h0).
by rewrite -addq_frac.
Qed.

(* Negation *)
Lemma opp_rationalE : {morph \pi_rat%C : a / (- a)%C >-> - a }.
Proof. by rewrite /= /normalize => a; rewrite -oppq_frac. Qed.

(* Multiplication *)
Lemma mul_rationalE : {morph \pi_rat%C : a b / (a * b)%C >-> a * b }.
Proof. 
rewrite /= /normalize /valr => [[[a1 a2]] /= h1 [[b1 b2]] /= h2].
have ha2_neq0 : a2 != 0 by apply/negP => h0; move: h1; rewrite (eqP h0).
have hb2_neq0 : b2 != 0 by apply/negP => h0; move: h2; rewrite (eqP h0).
by rewrite -mulq_frac.
Qed.

(* Inverse *)
Lemma inv_rationalE : {morph \pi_rat%C : a / (a^-1)%C >-> a^-1 }.
Proof. 
rewrite /= /normalize /valr  => [[[a1 a2]] /= h1].
have [->|a1_neq0] := altP (a1 =P 0). 
  by rewrite /inv_rational_subdef valqK fracq0 frac0q invr0.
rewrite /GRing.inv /= invq_frac //= /inv_rational_subdef ?valqK //.
by apply/negP => ha2_eq0; move: h1; rewrite (eqP ha2_eq0).
Qed.

(* Sub *)
Lemma sub_rationalE : {morph \pi_rat%C : a b / (a - b)%C >-> a - b }.
Proof. 
move=> a b.
by rewrite /sub /SubRational /sub_rational add_rationalE opp_rationalE.
Qed.

(* Div *)
Lemma div_rationalE : {morph \pi_rat%C : a b / (a / b)%C >-> a / b }.
Proof. 
move=> a b.
by rewrite /div /DivRational /div_rational mul_rationalE inv_rationalE.
Qed.


(* TODO: 
     - normq
     - le_rat
     - lt_rat
*)

End rational.

(* The concrete implementation: Refine rat' to B * B where B refines int *)
Section refines.

(* B is a type that should implement int *)
Variables (A B : Type).

(* Build a context with proper sharing and the necessary refinements *)
Context `{refinement_of int A B}
        `{Mul B, Add B, One B, Zero B, Comp B}
        `{!refines 0%R 0%C, !refines 1 1%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b}, refines (x + y)%R (a + b)%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b}, refines (x * y)%R (a * b)%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b}, refines (x == y)%R (a == b)%C}.

Definition RAT := (B * B)%type.

Definition rational_implem (a b : B) (r : rational)
  `{!refines (valr r).1 a, !refines (valr r).2 b} : RAT := (a, b)%C.

(* This FAILS, ... for now ..., but the solution is commmmming !! *)
Global Program Instance rational_has_implem : has_implem rational RAT :=
  @HasImplem _ _ rational_implem _.
Obligation 1.
rewrite /rational_implem => x y /= h; apply/valr_inj.
move: (valr x) (valr y) h => [a b] [c d] /= [h1 h2].
by have [-> ->] := (repr_inj (implem_inj h1), repr_inj (implem_inj h2)).
Qed.

Global Program Instance RAT_refinement_of_rat : refinement_of rat rational RAT := Refinement.

Global Program Instance Zero_BB : Zero RAT := (0%C,1%C).
Global Program Instance ZeroMorph_BB : refines (0 : rat)%R (0 : RAT)%C := Refines (0 : rational)%C _ _.
Next Obligation.
rewrite /rational_implem /=.



by rewrite /zero /Zero_BB !implemE.
Qed.

(* Global Program Instance ZeroMorph_rat : implem_of (0 : rat) (0 : B*B)%C. *)
(* Obligation 1. *)
(* exact: (@MorphImplem0 rat). *)
(* Qed. *)

Global Program Instance AddBB : Add (B * B) := fun x y => (x.1 * y.2 + y.1 * x.2, x.2 * y.2)%C.

(* Morphism from rat' to B * B for addition *)
Global Program Instance AddMorphBB (x y : rational) (a b : B * B) (xa : implem_of x a) (yb : implem_of y b) :
  implem_of (x + y)%C (a + b)%C.
Obligation 1.
rewrite /implem /= /rat'_implem /=.
move: x y xa yb =>  [[/= nx dx dx_gt0]] [[/= ny dy dy_gt0]].
rewrite /implem_of /= {1 2}/implem /= /rat'_implem /=.
do ?[move=> []; rewrite -2!/(implem_of _ _) => ? ?].
by rewrite !implemE.
Qed.

Global Program Instance CompBB : Comp (B * B) := fun x y => (x.1 * y.2 == x.2 * y.1)%C.

(* Morphism from rat' to B * B for addition *)
Global Program Instance CompMorphBB (x y : rational) (a b : B * B) (xa : implem_of x a) (yb : implem_of y b) :
  implem_of (x == y)%C (a == b)%C.
Obligation 1.
rewrite /implem /= /rat'_implem /=.
move: x y xa yb =>  [[/= nx dx dx_gt0]] [[/= ny dy dy_gt0]].
rewrite /implem_of /= {1 2}/implem /= /rat'_implem /=.
do ?[move=> []; rewrite -2!/(implem_of _ _) => ? ?].
by rewrite !implemE.
Qed.
(* Print HintDb typeclass_instances. *)

(* This is not true as we have no morph for addition on rat to addition on rational *)
(* Global Program Instance AddMorph_rat : *)
(*   Morph (implem ==> implem ==> implem) (fun x y : rat => x + y) (fun x y : B * B => x + y)%C. *)
(* Obligation 1. *)
(* exact: MorphTrans2. *)
(* Qed. *)

End refines.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0%C + 0%C + 0%C)%C : Z * Z. *)


Section tests.
Require Import ZArith ssrint binint.

Eval compute in (0%C + 0%C + 0%C)%C : Z * Z.

Lemma bool_implem P (b : bool) : P (\implem_bool b)%C -> P b.
Proof. done. Qed.

Goal (1000%:Q + 1500%:Q = 2500%:Q).
Proof.
apply/eqP.
apply: bool_implem.
rewrite implemE.