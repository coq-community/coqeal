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
Section rational.

Definition rational (B : Type) := (B * B)%type.
Local Notation rat' := (rational int).

(* Canonical rational_subType := Eval hnf in [subType for valr]. *)

(* Lemma val_inj : injective valr. *)
(* Proof. exact: val_inj. Qed. *)

(* rat_to_rat' = repr *) (* rat'_to_rat = \pi_rat *)
Definition rat_to_rat' (r : rat) : rat' := (val r).
Definition rat'_to_rat (r : rat') : option rat :=
  if r.2 == 0 then None else Some (fracq r).

Lemma rat'_to_ratK : pcancel rat_to_rat' rat'_to_rat.
Proof. move=> x; rewrite /rat'_to_rat; case:ifPn => //.
admit.
admit.
Qed.

(* We have a quotient type where rat is the quotients of rat' *)
Global Instance rat_refinement : refinement_of rat rat' := 
  Refinement rat'_to_ratK.

Section rational.
Variable B : Type.
Context `{zero B, one B, add B, opp B, mul B, eq B}.
Local Notation ratB := (rational B).

(* Zero *)
Definition zero_rational : ratB := (0, 1)%C.
Global Program Instance zero_ratB : zero ratB := zero_rational.

(* One *)
Definition one_rational : ratB := (1, 1)%C.
Global Program Instance one_ratB : one ratB := one_rational.

(* Add *)
Definition add_rational (x y : ratB) : ratB :=
   (x.1 * y.2 + y.1 * x.2, x.2 * y.2)%C.
Global Program Instance add_ratB : add ratB := add_rational.

(* Mul *)
Definition mul_rational (x y : ratB) : ratB := (x.1 * y.1, x.2 * y.2)%C.
Global Program Instance mul_ratB : mul ratB := mul_rational.

(* Opp *)
Definition opp_rational (x : ratB) : ratB := (- x.1, x.2)%C.
Global Program Instance opp_ratB : opp ratB := opp_rational.

(* Comp *)
Definition eq_rational (x y : ratB) : bool := (x.1 * y.2 == x.2 * y.1)%C.
Global Program Instance eq_ratB : eq ratB := eq_rational.

(* Inv *)
Definition inv_rational (x : ratB) : ratB :=
  (if (x.1 == 0)%C then 0%C else (x.2, x.1)%C).
Global Program Instance inv_ratB : inv ratB := inv_rational.

(* Subtraction *)
Definition sub_rational (a b : ratB) : ratB := (a + - b)%C.
Global Program Instance sub_ratB : sub ratB := sub_rational.

(* Division *)
Definition div_rational (a b : ratB) : ratB := (a * b^-1)%C.
Global Program Instance div_ratB : div ratB := div_rational.

End rational.

Local Notation rati := (rational int).

Program Instance : zero int := 0%R.
Program Instance : one int  := 1%R.
Program Instance : add int  := +%R.
Program Instance : opp int  := -%R.
Program Instance : mul int  := *%R.
Program Instance : eq int   := eqtype.eq_op.

Definition zero_rational_indom : (0%C : rati).2 != 0. Proof. done. Qed.
Definition one_rational_indom : (1%C : rati).2 != 0. Proof. done. Qed.

(*
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
*)

(* Addition *)

(* Adding and then normalizing should be the same as first normalizing and
   then adding *)
(* Lemma add_rationalE : {morph \pi_rat%C : a b / (a + b)%C >-> a + b }. *)
(* Proof. *)
(* rewrite /= /rat'_to_rat /valr => [[[a1 a2]] /= h1 [[b1 b2]] /= h2]. *)
(* have ha2_neq0 : a2 != 0 by apply/negP => h0; move: h1; rewrite (eqP h0). *)
(* have hb2_neq0 : b2 != 0 by apply/negP => h0; move: h2; rewrite (eqP h0). *)
(* by rewrite -addq_frac. *)
(* Qed. *)

(* (* Negation *) *)
(* Lemma opp_rationalE : {morph \pi_rat%C : a / (- a)%C >-> - a }. *)
(* Proof. by rewrite /= /rat'_to_rat => a; rewrite -oppq_frac. Qed. *)

(* (* Multiplication *) *)
(* Lemma mul_rationalE : {morph \pi_rat%C : a b / (a * b)%C >-> a * b }. *)
(* Proof.  *)
(* rewrite /= /rat'_to_rat /valr => [[[a1 a2]] /= h1 [[b1 b2]] /= h2]. *)
(* have ha2_neq0 : a2 != 0 by apply/negP => h0; move: h1; rewrite (eqP h0). *)
(* have hb2_neq0 : b2 != 0 by apply/negP => h0; move: h2; rewrite (eqP h0). *)
(* by rewrite -mulq_frac. *)
(* Qed. *)

(* (* Inverse *) *)
(* Lemma inv_rationalE : {morph \pi_rat%C : a / (a^-1)%C >-> a^-1 }. *)
(* Proof.  *)
(* rewrite /= /rat'_to_rat /valr  => [[[a1 a2]] /= h1]. *)
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
Variable (B : Type).

(* Build a context with proper sharing and the necessary refinements *)
Context `{zero B, one B, add B, opp B, mul B, eq B}.
Context `{refinement_of int B}.

Context `{!refines 0%R 0%C, !refines 1 1%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x + y)%R (a + b)%C,
          forall (x : int) (a : B) `{!refines x a},
            refines (- x)%R (- a)%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x * y)%R (a * b)%C,
          forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x == y)%R (a == b)%C}.

(*
Local Notation ratA' := {r : ratA | \pi%C r.2 != 0}.
*)

Local Notation ratB := (rational B).

(*
Definition rational_implem (r : ratA') : ratB := 
  (implem (val r).1, implem (val r).2).

Global Program Instance rational_has_implem : has_implem ratA' ratB :=
  @HasImplem _ _ rational_implem _.
Obligation 1.
rewrite /rational_implem => x y /= h; apply/val_inj => /=.
move: (val x) (val y) h => [a b] [c d] /= [h1 h2] /=.
by have [-> ->] := (implem_inj h1, implem_inj h2).
Qed.
*)

(* Definition rat'_pi (r : rat') : rat := ((val r).1)%:Q / ((val r).2)%:Q. *)
(* Definition rat'_repr (r : rat) : rat' := exist _ (numq r, denq r) (denq_neq0 _). *)
(* Lemma rat'_reprK : cancel rat'_repr rat'_pi. *)
(* Proof. by move=> r; rewrite /rat'_pi /=; case: ratP. Qed. *)
(* Global Program Instance quotient_rat' : quotient_of rat' rat := QuotClass rat'_reprK. *)

Definition rational_spec (r : ratB) : option rat :=
  match \spec_int%C r.1, \spec_int%C r.2 with
  | Some u, Some v => if v == 0 then None else Some (u%:Q / v%:Q)
  | _, _ => None
  end.

Definition rational_implem (r : rat) : ratB := 
  (\implem%C (numq r), \implem%C (denq r)).

Lemma rational_implemK : pcancel rational_implem rational_spec.
Proof.
by move=> r; rewrite /rational_spec /rational_implem /= !implemK; case: ratP.
Qed.

Global Program Instance refinement_rat : refinement_of rat ratB := 
  Refinement rational_implemK.

Global Program Instance refines_rat_0 : refines (0 : rat)%R (0 : ratB)%C.
Next Obligation. by rewrite /rational_spec !spec_refines oner_eq0. Qed.

Lemma refines_rat_inv x a b :
  refines x (a,b) -> exists u v : int,
    [/\ refines u a, refines v b, v != 0 & u%:Q / v %:Q = x].
Proof.
move=> ref_x.
move: (@spec_refines _ _ _ _ _ ref_x).
rewrite /= /rational_spec /=.
(* my ssr is still poor... *)
generalize (refl_equal (\spec_(int)%C a)).
case: {2 3}(\spec_(int)%C a) => // u eq_u.
generalize (refl_equal (\spec_(int)%C b)).
case: {2 3}(\spec_(int)%C b) => // v eq_v.
case: ifPn=> // nz_v0 eq_x.
exists u; exists v; split=> //.
by injection eq_x.
Qed.

(* Morphism from rat' to B * B for addition *)
Global Program Instance refines_rat_add  (x y : rat) (a b : ratB) 
    (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Next Obligation. 
case: a xa => a1 a2 xa.
case: b yb => b1 b2 yb.
rewrite /add_op /add_ratB /add_rational /= /rational_spec /=.
case/refines_rat_inv: (xa) => [u1 [u2 [ref_u1 ref_u2 nz_u2 eq_x]]].
case/refines_rat_inv: (yb) => [v1 [v2 [ref_v1 ref_v2 nz_v2 eq_y]]].
rewrite !spec_refines.
case: ifP => [|_].
  by rewrite mulf_eq0 (negbTE nz_u2) (negbTE nz_v2).
rewrite -eq_x -eq_y.
(* the remaining proof is purely algebraic on ssr objects *)
by rewrite addf_div ?intq_eq0 // !(rmorphM,rmorphD).
Qed.

Global Program Instance refines_rat_eq (x y : rat) (a b : ratB) 
    (xa : refines x a) (yb : refines y b) : refines (x == y)%R (a == b)%C.
Next Obligation. admit. Qed.

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
End rational.
(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0%C + 0%C + 0%C)%C : Z * Z. *)


Section tests.
(*
Require Import ZArith ssrint binint.

Eval compute in (0%C + 0%C + 0%C)%C : Z * Z.
*)

(*
Lemma bool_implem P (b : bool) : P (\implem_bool b)%C -> P b.
Proof. done. Qed.
*)

Lemma bool_refine (b b' : bool) `{!refines b b'} : b = b'.
Proof.
move: {refines0} (@spec_refines _ _ _ _ _ refines0).
by case:b ; case: b'.
Qed.

(* Fake implementation of intr to test inference *)
Variable intr_impl : forall B, int -> B.

(*
Instance intr_refines {R : ringType} {R'} x `{H : quotient_of R' R} :
  refines (intr x) (intr_impl R' x).
admit.
Qed.
*)

(*
Instance intr_refines B (x : int) `{quotient_of B int} :
  refines x%:Q (intr_impl B x).
admit.
Qed.

Goal (2500%:Q = 2500%:Q).
Proof.
apply/eqP.
Check (refines_rat_comp _ _ _ _ (intr_refines (Posz 2500))
(intr_refines (Posz 2500))).


rewrite [_ == _](@bool_refine _ _ (refines_rat_comp _ _ _ _ (intr_refines (Posz 2500))
(intr_refines (Posz 2500)))).

(* missing refinement for intr and default refinement for naturals *)
Qed.

Goal (1000%:Q + 1500%:Q = 2500%:Q).
Proof.
apply/eqP.
rewrite [_ == _](bool_refine refines_rat_comp).
(* missing refinement for intr and default refinement for naturals *)
Qed.
*)

End tests.