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
Local Open Scope quotient_scope.
Local Open Scope signature_scope.

Import GRing.Theory.
Import Num.Theory.

(* rational - Non normalized rational numbers *)
Section rational.

Definition rational (B : Type) := (B * B)%type.
Local Notation rat' := {r : rational int | r.2 != 0}.

(* Canonical rational_subType := Eval hnf in [subType for valr]. *)

(* Lemma val_inj : injective valr. *)
(* Proof. exact: val_inj. Qed. *)

(* denormalize = repr *) (* normalize = \pi_rat *)
Definition denormalize (r : rat) : rat' := exist _ (val r) (denq_neq0 r).
Definition normalize (r : rat') : rat := fracq (val r).

Lemma normalizeK : cancel denormalize normalize.
Proof. by move=> x; rewrite /normalize /denormalize valqK. Qed.

(* We have a quotient type where rat is the quotients of rat' *)
Global Instance rat_quotient : quotient_of rat' rat := QuotClass normalizeK.

Section rational.
Variable B : Type.
Context `{Zero B, One B, Add B, Opp B, Mul B, Comp B}.
Local Notation ratB := (rational B).

(* Zero *)
Definition zero_rational : ratB := (0, 1)%C.
Global Program Instance ZeroRational : Zero ratB := zero_rational.

(* One *)
Definition one_rational : ratB := (1, 1)%C.
Global Program Instance OneRational : One ratB := one_rational.

(* Add *)
Definition add_rational (x y : ratB) : ratB :=
   (x.1 * y.2 + y.1 * x.2, x.2 * y.2)%C.
Global Program Instance AddRational : Add ratB := add_rational.

(* Mul *)
Definition mul_rational (x y : ratB) : ratB := (x.1 * y.1, x.2 * y.2)%C.
Global Program Instance MulRational : Mul ratB := mul_rational.

(* Opp *)
Definition opp_rational (x : ratB) : ratB := (- x.1, x.2)%C.
Global Program Instance OppRational : Opp ratB := opp_rational.

(* Comp *)
Definition comp_rational (x y : ratB) : bool := (x.1 * y.2 == x.2 * y.1)%C.
Global Program Instance CompRational : Comp ratB := comp_rational.

(* Inv *)
Definition inv_rational (x : ratB) : ratB :=
  (if (x.1 == 0)%C then 0%C else (x.2, x.1)%C).
Global Program Instance InvRational : Inv ratB := inv_rational.

(* Subtraction *)
Definition sub_rational (a b : ratB) : ratB := (a + - b)%C.
Global Program Instance SubRational : Sub ratB := sub_rational.

(* Division *)
Definition div_rational (a b : ratB) : ratB := (a * b^-1)%C.
Global Program Instance DivRational : Div ratB := div_rational.

End rational.

Local Notation rati := (rational int).

Program Instance : Zero int := 0%R.
Program Instance : One int := 1%R.
Program Instance : Add int := +%R.
Program Instance : Opp int := -%R.
Program Instance : Mul int := *%R.
Program Instance : Comp int := eq_op.

Definition zero_rational_indom : (0%C : rati).2 != 0. Proof. done. Qed.
Definition one_rational_indom : (1%C : rati).2 != 0. Proof. done. Qed.

Definition add_rational_indom (x y : rat') : (val x + val y)%C.2 != 0.
Proof. by move: x y => [a a0] [b b0]; rewrite mulf_neq0. Qed.

Definition mul_rational_indom (x y : rat') : (val x * val y)%C.2 != 0.
Proof. by move: x y => [a a0] [b b0]; rewrite mulf_neq0. Qed.

Definition opp_rational_indom (x : rat') : (- val x)%C.2 != 0.
Proof. by case: x. Qed.

Definition inv_rational_indom (x : rat') : (val x)^-1%C.2 != 0.
Proof.
move: x => [x px] /=.
rewrite /inv /InvRational /inv_rational -[(_ == 0)%C]/(_ == 0).
by have [] := altP (x.1 =P 0).
Qed.

(* Addition *)

(* Adding and then normalizing should be the same as first normalizing and
   then adding *)
(* Lemma add_rationalE : {morph \pi_rat%C : a b / (a + b)%C >-> a + b }. *)
(* Proof. *)
(* rewrite /= /normalize /valr => [[[a1 a2]] /= h1 [[b1 b2]] /= h2]. *)
(* have ha2_neq0 : a2 != 0 by apply/negP => h0; move: h1; rewrite (eqP h0). *)
(* have hb2_neq0 : b2 != 0 by apply/negP => h0; move: h2; rewrite (eqP h0). *)
(* by rewrite -addq_frac. *)
(* Qed. *)

(* (* Negation *) *)
(* Lemma opp_rationalE : {morph \pi_rat%C : a / (- a)%C >-> - a }. *)
(* Proof. by rewrite /= /normalize => a; rewrite -oppq_frac. Qed. *)

(* (* Multiplication *) *)
(* Lemma mul_rationalE : {morph \pi_rat%C : a b / (a * b)%C >-> a * b }. *)
(* Proof.  *)
(* rewrite /= /normalize /valr => [[[a1 a2]] /= h1 [[b1 b2]] /= h2]. *)
(* have ha2_neq0 : a2 != 0 by apply/negP => h0; move: h1; rewrite (eqP h0). *)
(* have hb2_neq0 : b2 != 0 by apply/negP => h0; move: h2; rewrite (eqP h0). *)
(* by rewrite -mulq_frac. *)
(* Qed. *)

(* (* Inverse *) *)
(* Lemma inv_rationalE : {morph \pi_rat%C : a / (a^-1)%C >-> a^-1 }. *)
(* Proof.  *)
(* rewrite /= /normalize /valr  => [[[a1 a2]] /= h1]. *)
(* have [->|a1_neq0] := altP (a1 =P 0).  *)
(*   by rewrite /inv_rational_subdef valqK fracq0 frac0q invr0. *)
(* rewrite /GRing.inv /= invq_frac //= /inv_rational_subdef ?valqK //. *)
(* by apply/negP => ha2_eq0; move: h1; rewrite (eqP ha2_eq0). *)
(* Qed. *)

(* (* Sub *) *)
(* Lemma sub_rationalE : {morph \pi_rat%C : a b / (a - b)%C >-> a - b }. *)
(* Proof.  *)
(* move=> a b. *)
(* by rewrite /sub /SubRational /sub_rational add_rationalE opp_rationalE. *)
(* Qed. *)

(* (* Div *) *)
(* Lemma div_rationalE : {morph \pi_rat%C : a b / (a / b)%C >-> a / b }. *)
(* Proof.  *)
(* move=> a b. *)
(* by rewrite /div /DivRational /div_rational mul_rationalE inv_rationalE. *)
(* Qed. *)


(* TODO: 
     - normq
     - le_rat
     - lt_rat
*)


(* Class parametric (T : forall A, Type) := { *)
(*   parametricP : forall (A B : Type) (P : forall A, Type -> Type), P A (T A) -> P B (T B) *)
(* }. *)

(* Definition parametric_repr A B (T : forall A, Type) `{quotient_of A B} (ta : T A) : T B := *)
  

(* Lemma rat_parametric_quotient A B (T : forall A, Type) :  *)
(*   quotient_of A B -> quotient_of (T A) (T B). *)
(* Proof. *)
(* move=> QAB. *)



(* The concrete implementation: Refine rat' to B * B where B refines int *)
Section refines.

(* B is a type that should implement int *)
Variables (A B : Type).

(* Build a context with proper sharing and the necessary refinements *)
Context `{Zero B, One B, Add B, Opp B, Mul B, Comp B}.
Context `{refinement_of int A B}
        `{!refines 0%R 0%C, !refines 1 1%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x + y)%R (a + b)%C,
          forall (x : int) (a : B) `{!refines x a},
            refines (- x)%R (- a)%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x * y)%R (a * b)%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x == y)%R (a == b)%C}.

Local Notation ratA := (rational A).
Local Notation ratA' := {r : ratA | \pi%C r.2 != 0}.
Local Notation ratB := (rational B).

Definition rational_implem (r : ratA') : ratB := 
  (implem (val r).1, implem (val r).2).

Global Program Instance rational_has_implem : has_implem ratA' ratB :=
  @HasImplem _ _ rational_implem _.
Obligation 1.
rewrite /rational_implem => x y /= h; apply/val_inj => /=.
move: (val x) (val y) h => [a b] [c d] /= [h1 h2] /=.
by have [-> ->] := (implem_inj h1, implem_inj h2).
Qed.

(* Definition rat'_pi (r : rat') : rat := ((val r).1)%:Q / ((val r).2)%:Q. *)
(* Definition rat'_repr (r : rat) : rat' := exist _ (numq r, denq r) (denq_neq0 _). *)
(* Lemma rat'_reprK : cancel rat'_repr rat'_pi. *)
(* Proof. by move=> r; rewrite /rat'_pi /=; case: ratP. Qed. *)
(* Global Program Instance quotient_rat' : quotient_of rat' rat := QuotClass rat'_reprK. *)

Definition rational_pi (r : ratA') : rat := (\pi%C (val r).1)%:Q / (\pi%C (val r).2)%:Q.
Program Definition rational_repr (r : rat) : ratA' := exist _ (repr (numq r), repr (denq r)) _.
Next Obligation. by rewrite reprK denq_neq0. Qed.

Lemma rational_reprK : cancel rational_repr rational_pi.
Proof.
by move=> r; rewrite /rational_pi /rational_repr /= !reprK; case: ratP.
Qed.

Global Program Instance quotient_rat : quotient_of ratA' rat := QuotClass rational_reprK.

Global Program Instance refinement_of_rat : refinement_of rat ratA' ratB :=
  Refinement.

Global Program Instance refines_rat_0 : refines (0 : rat)%R (0 : ratB)%C := 
  Refines (exist _ (refine_repr 0%R 0%C, refine_repr 1 1%C) _) _ _.
Next Obligation. by rewrite refines_pi. Qed.
Next Obligation. by rewrite /rational_pi /= !refines_pi. Qed.
Next Obligation. by rewrite /rational_implem /= !refines_implem. Qed.

(* Global Program Instance ZeroMorph_rat : implem_of (0 : rat) (0 : B*B)%C. *)
(* Obligation 1. *)
(* exact: (@MorphImplem0 rat). *)
(* Qed. *)

(* Morphism from rat' to B * B for addition *)
Global Program Instance refines_rat_add  (x y : rat) (a b : ratB) 
    (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Global Program Instance refines_rat_comp (x y : rat) (a b : ratB) 
    (xa : refines x a) (yb : refines y b) : refines (x == y)%R (a == b)%C.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.


(* Global Program Instance AddMorphBB (x y : rational) (a b : B * B) (xa : implem_of x a) (yb : implem_of y b) : *)
(*   implem_of (x + y)%C (a + b)%C. *)
(* Obligation 1. *)
(* rewrite /implem /= /rat'_implem /=. *)
(* move: x y xa yb =>  [[/= nx dx dx_gt0]] [[/= ny dy dy_gt0]]. *)
(* rewrite /implem_of /= {1 2}/implem /= /rat'_implem /=. *)
(* do ?[move=> []; rewrite -2!/(implem_of _ _) => ? ?]. *)
(* by rewrite !implemE. *)
(* Qed. *)

(* Global Program Instance CompBB : Comp (B * B) := fun x y => (x.1 * y.2 == x.2 * y.1)%C. *)

(* (* Morphism from rat' to B * B for addition *) *)
(* Global Program Instance CompMorphBB (x y : rational) (a b : B * B) (xa : implem_of x a) (yb : implem_of y b) : *)
(*   implem_of (x == y)%C (a == b)%C. *)
(* Obligation 1. *)
(* rewrite /implem /= /rat'_implem /=. *)
(* move: x y xa yb =>  [[/= nx dx dx_gt0]] [[/= ny dy dy_gt0]]. *)
(* rewrite /implem_of /= {1 2}/implem /= /rat'_implem /=. *)
(* do ?[move=> []; rewrite -2!/(implem_of _ _) => ? ?]. *)
(* by rewrite !implemE. *)
(* Qed. *)
(* (* Print HintDb typeclass_instances. *) *)

(* (* This is not true as we have no morph for addition on rat to addition on rational *) *)
(* (* Global Program Instance AddMorph_rat : *) *)
(* (*   Morph (implem ==> implem ==> implem) (fun x y : rat => x + y) (fun x y : B * B => x + y)%C. *) *)
(* (* Obligation 1. *) *)
(* (* exact: MorphTrans2. *) *)
(* (* Qed. *) *)

End refines.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0%C + 0%C + 0%C)%C : Z * Z. *)


Section tests.
Require Import ZArith ssrint binint.

Eval compute in (0%C + 0%C + 0%C)%C : Z * Z.

Lemma bool_implem P (b : bool) : P (\implem_bool b)%C -> P b.
Proof. done. Qed.

Lemma bool_refine (b b' : bool) `{refines b b'} : b = b'.
Proof.
Admitted.

Goal (1000%:Q + 1500%:Q = 2500%:Q).
Proof.
apply/eqP.
rewrite [_ == _]bool_refine.
(* missing refinement for intr and default refinement for naturals *)
Qed.