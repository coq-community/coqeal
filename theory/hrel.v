(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset bigop.

(** This file implements the basic theory of refinements *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope rel_scope with rel.

(* Shortcut for triggering typeclass resolution *)
Ltac tc := do 1?typeclasses eauto.

Require Import Setoid Basics Equivalence Morphisms.

(***************************)
(* Heterogeneous Relations *)
(***************************)
Section HeterogeneousRelations.

Definition sub_hrel {A B : Type} (R R' : A -> B -> Prop) :=
  forall (x : A) (y : B), R x y -> R' x y.
Arguments sub_hrel A B R%rel R'%rel.
Notation "X <= Y" := (sub_hrel X Y) : rel_scope.

Lemma sub_Falsel {A B} (R : A -> B -> Prop) : ((fun _ _ => False) <= R)%rel.
Proof. done. Qed.

Lemma sub_Truer {A B} (R : A -> B -> Prop) : (R <= (fun _ _ => True))%rel.
Proof. done. Qed.

Lemma sub_eql {A : Type} (R : A -> A -> Prop) `{!Reflexive R} : (eq <= R)%rel.
Proof. by move=> x _ <-. Qed.

Inductive eq_hrel {A B} (R R' : A -> B -> Prop) :=
  EqHrel of (R <= R')%rel & (R' <= R)%rel.
Arguments eq_hrel A B R%rel R'%rel.
Notation "X <=> Y" := (eq_hrel X Y) (format "X  <=>  Y", at level 95) : rel_scope.

Lemma eq_hrelRL {A B} (R R' : A -> B -> Prop) : (R <=> R')%rel -> (R <= R')%rel.
Proof. by case. Qed.

Lemma eq_hrelLR {A B} (R R' : A -> B -> Prop) : (R <=> R')%rel -> (R' <= R)%rel.
Proof. by case. Qed.

Global Instance sub_hrel_partialorder A B : PreOrder (@sub_hrel A B).
Proof. by constructor=> [R|R S T RS ST a b /RS /ST]. Qed.

Global Instance eq_hrel_equiv A B : Equivalence (@eq_hrel A B).
Proof.
constructor=> [R|R S []|R S T [RS SR] [ST TS]];
by do ?split => //; transitivity S.
Qed.

Global Instance sub_hrel_proper A B : Proper (eq_hrel ==> eq_hrel ==> iff) (@sub_hrel A B).
Proof.
move=> R S [RS SR] T U [TU UT]; split=> [RT|SU].
  by transitivity T => //; transitivity R => //.
by transitivity U => //; transitivity S => //.
Qed.

Global Instance sub_hrel_partial_order A B : PartialOrder (@eq_hrel A B ) (@sub_hrel A B).
Proof. by move=> R S; split=> [[RS SR]|[]]; constructor. Qed.

Definition comp_hrel {A B C} (R : A -> B -> Prop) (R' : B -> C -> Prop) : A -> C -> Prop :=
  fun a c => exists b, R a b /\ R' b c.

Arguments comp_hrel A B C R%rel R'%rel _ _.
Notation "X \o Y" := (comp_hrel X Y) : rel_scope.

Lemma comp_hrelP {A B C} (R : A -> B -> Prop) (R' : B -> C -> Prop)
  (b : B) (a : A) (c : C) : R a b -> R' b c -> (R \o R')%rel a c.
Proof. by exists b. Qed.

Global Instance comp_hrel_sub_proper {A B C} :
  Proper (sub_hrel ==> sub_hrel ==> sub_hrel) (@comp_hrel A B C).
Proof.
move=> R S RS T U TU x z [y [Rxy Tyz]].
by exists y; split; [apply: RS|apply: TU].
Qed.

Global Instance comp_hrel_eq_proper {A B C} :
  Proper (eq_hrel ==> eq_hrel ==> eq_hrel) (@comp_hrel A B C).
Proof. by move=> ?? [??] ?? [??]; split; apply: comp_hrel_sub_proper. Qed.

Lemma comp_eqr {A B} (R : A -> B -> Prop) : (R \o eq <=> R)%rel.
Proof. by split=> [x y [y' [? <-]] //|x y Rxy]; exists y. Qed.

Lemma comp_eql {A B} (R : A -> B -> Prop) : (eq \o R <=> R)%rel.
Proof. by split=> [x y [x' [<- ?]] //|x y Rxy]; exists x. Qed.

Definition fun_hrel {A B} (f : B -> A) : A -> B -> Prop :=
  fun a b => f b = a.

Definition ofun_hrel {A B} (f : B -> option A) : A -> B -> Prop :=
  fun a b => f b = Some a.

End HeterogeneousRelations.

Notation "X \o Y" := (comp_hrel X Y) : rel_scope.
Notation "X <= Y" := (sub_hrel X Y) : rel_scope.
Notation "X <=> Y" := (eq_hrel X Y) (format "X  <=>  Y", at level 95) : rel_scope.

(*****************************************)
(* Respectful on heterogeneous relations *)
(*****************************************)
Definition hrespectful {A B C D : Type}
  (R : A -> B -> Prop) (R' : C -> D -> Prop) : (A -> C) -> (B -> D) -> Prop :=
  Classes.Morphisms.respectful_hetero _ _ _ _ R (fun x y => R').

Arguments hrespectful {A B C D} R%rel R'%rel _ _.
Notation " R ==> S " := (@hrespectful _ _ _ _ R S)
    (right associativity, at level 55) : rel_scope.

Global Instance hrespectful_sub_proper {A B C D} :
   Proper (sub_hrel --> sub_hrel ==> sub_hrel) (@hrespectful A B C D).
Proof.
move=> R S /= SR T U TU x y /= RTxy a b Sab.
by apply: TU; apply: RTxy; apply: SR.
Qed.

Global Instance hrespectful_proper {A B C D} :
   Proper (eq_hrel ==> eq_hrel ==> eq_hrel) (@hrespectful A B C D).
Proof. by move=> ?? [??] ?? [??]; split; apply: hrespectful_sub_proper. Qed.

Lemma sub_hresp_comp  {A B C} (R1 R1': A -> B -> Prop) (R2 R2': B -> C -> Prop) :
  (((R1 ==> R1') \o (R2 ==> R2')) <= ((R1 \o R2) ==> (R1' \o R2')))%rel.
Proof.
move=> f h [g [rfg rgh]] x z [y [rxy ryz]]; exists (g y).
by split; [apply: rfg | apply: rgh].
Qed.
