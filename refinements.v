(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop.
Require Import Morphisms.
Require generic_quotient.

Module qT := generic_quotient.

(** This file implements the basic theory of refinements using operational
type classes and arbitrary arity morphism lemmas 

Implem A B  == B implements A, there is a function implem : A -> B 
Refines A B == B refines A, implem is injective 
Morph R f g == ?
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Reserved Notation "| f |" (at level 10, format "| f |"). *)
(* Reserved Notation "R \==> S" (at level 55, right associativity). *)
Reserved Notation "\implem_ B" (at level 0, format "\implem_ B").
Reserved Notation "\implem" (at level 0, format "\implem").
Reserved Notation "\pi_ Q" (at level 0, format "\pi_ Q").
Reserved Notation "\pi" (at level 0, format "\pi").

Delimit Scope computable_scope with C.
Delimit Scope signature_scope with S.

Local Open Scope ring_scope.

Import GRing.Theory.

Class has_implem A B := HasImplem {implem : A -> B; implem_inj : injective implem}.
Notation "\implem_ B" := (@implem _ B _) : computable_scope.
Notation "\implem" := (@implem _ _ _) (only parsing) : computable_scope.

Global Program Instance has_implem_trans {A B C} `{has_implem A B, has_implem B C} :
  has_implem A C := @HasImplem _ _ (implem \o implem) _.
Obligation 1. by apply: inj_comp; apply: implem_inj. Qed.

Class quotient_of T qT := QuotClass {
  repr : qT -> T;
  quot_pi : T -> qT;
  _ : cancel repr quot_pi
}.
Notation "\pi_ Q" := (@quot_pi _ Q _) : computable_scope.
Notation "\pi" := (@quot_pi _ _ _) (only parsing) : computable_scope.

Lemma reprK  (T Q : Type) (qT : quotient_of T Q) : cancel repr \pi%C.
Proof. by case: qT. Qed.

Lemma repr_inj (T Q : Type) (qT : quotient_of T Q) : injective repr.
Proof. exact: (can_inj (reprK _)). Qed.

Global Program Instance quotType_quotient_of B (A : qT.quotType B) : quotient_of B (qT.quot_sort A) :=
  QuotClass (@qT.reprK _ _).

Class refinement_of (A B C : Type) `{quotient_of B A} `{has_implem B C} := Refinement {}.
Arguments refinement_of A B C {_ _}.
Arguments Refinement {_ _ _ _ _}.

Class refines (A B C : Type) `{refinement_of A B C} (a : A) (c : C) := Refines {
  refine_repr : B;
  refines_pi : \pi_A%C refine_repr = a;
  refines_implem : \implem_C%C refine_repr = c
}.

Arguments refine_repr {A B C _ _ _} a c {_}.
Arguments refines {A B C _ _ _} a c.
Arguments Refines {A B C _ _ _ _ _} refine_repr _ _.

Global Instance id_quot_class A : quotient_of A A := @QuotClass A A id id (fun _ => erefl).
(* Definition id_quotType A := QuotType A (@id_quot_class A). *)

Global Program Instance has_implem_bool : has_implem bool bool :=
  @HasImplem _ _ id (fun _ _ _ => erefl).
Global Program Instance bool_refinement_of_bool : refinement_of bool bool bool := Refinement.

Global Program Instance refines_bool (a : bool) : refines a a :=
  @Refines _ _ _ _ _ _ _ _ a _ _.

(* Local Open Scope computable_scope. *)

(* Instance implem_default A B `{Implem A B} (a : A) :  a (\implem_B%C a) | 999. *)
(* Proof. done. Qed. *)

Section Operations.

Local Open Scope signature_scope.

(* Zero arity operations, i.e. constants *)
Class Zero B := zero : B.
Local Notation "0" := zero : computable_scope.

Class One B := one_op : B.
Local Notation "1" := one_op : computable_scope.

(* Unary operations *)
Class Opp B := opp : B -> B.
Local Notation "-%C" := opp.
Local Notation "- x" := (opp x) : computable_scope.

Class Inv B := inv : B -> B.
Local Notation "x ^-1" := (inv x) : computable_scope.

(* Binary operations *)
Class Add B := add : B -> B -> B.
Local Notation "+%C" := add.
Local Notation "x + y" := (add x y) : computable_scope.

Class Sub B := sub : B -> B -> B.
Local Notation "x - y" := (sub x y) : computable_scope.

Class Mul B := mul : B -> B -> B.
Local Notation "*%C" := mul.
Local Notation "x * y" := (mul x y) : computable_scope.

Class Div B := div : B -> B -> B.
Local Notation "x / y" := (div x y) : computable_scope.

(* Comparisons *)
Class Comp B := comp : B -> B -> bool.
Local Notation "x == y" := (comp x y) : computable_scope.

End Operations.

Notation "0"      := zero : computable_scope.
Notation "1"      := one_op : computable_scope.
Notation "-%C"    := opp.
Notation "- x"    := (opp x) : computable_scope.
Notation "x ^-1"  := (inv x) : computable_scope.
Notation "+%C"    := add.
Notation "x + y"  := (add x y) : computable_scope.
Notation "x - y"  := (sub x y) : computable_scope.
Notation "*%C"    := mul.
Notation "x * y"  := (mul x y) : computable_scope.
Notation "x / y"  := (div x y) : computable_scope.
Notation "x == y" := (comp x y) : computable_scope.