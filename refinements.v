(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop.
Require Import Morphisms.
Require generic_quotient.

Module qT := generic_quotient.

(** This file implements the basic theory of refinements 

refinement_of A B == B is a refinement of A
refines a b       == a refines to b
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\implem_ A" (at level 0, format "\implem_ A").
Reserved Notation "\implem" (at level 0, format "\implem").
Reserved Notation "\spec_ B" (at level 0, format "\spec_ B").
Reserved Notation "\spec" (at level 0, format "\spec").

Delimit Scope computable_scope with C.

Local Open Scope ring_scope.

Import GRing.Theory.

Class refinement_of A B := RefinementClass {
  implem : A -> B;
  dom : pred B;
  spec : B -> option A;
  implemK : pcancel implem spec;
  domP : forall b, b \in dom = spec b
}.
Notation "\implem_ B" := (@implem _ B _) : computable_scope.
Notation "\implem" := (@implem _ _ _) (only parsing) : computable_scope.
Notation "\spec_ A" := (@spec A _ _) : computable_scope.
Notation "\spec" := (@spec _ _ _) (only parsing) : computable_scope.

Definition Refinement A B (implem : A -> B) (spec : B -> option A) 
  (p : pcancel implem spec) : refinement_of A B := 
  @RefinementClass _ _ _ (fun b => spec b) _ p (fun _ => erefl).

Lemma implem_inj A B `{refinement_of A B} : injective implem.
Proof. exact: (pcan_inj implemK). Qed.

Definition specd A B `{refinement_of A B} (a : A) (b : B) := odflt a (spec b).

Lemma implem_composeK A B C `{refinement_of A B, refinement_of B C} :
  pcancel (\implem_C \o \implem_B)%C (obind \spec_A \o \spec_B)%C.
Proof. by move=> a /=; rewrite implemK /= implemK. Qed.

Definition refinement_id A : refinement_of A A := 
  Refinement (fun _ => erefl).

Class refines {A B : Type} `{refinement_of A B} (a : A) (b : B) := Refines {
  spec_refines : \spec%C b = Some a
}.

Lemma specd_refines A B `{refinement_of A B} (a : A) (b : B) `{!refines a b}: 
  specd a b = a.
Proof. by rewrite /specd spec_refines. Qed.


Global Instance refinement_bool : refinement_of bool bool := refinement_id bool.
Global Program Instance refines_bool (a : bool) : refines a a.

Program Definition refinement_trans A B C
  (rab : refinement_of A B) (rbc : refinement_of B C) : refinement_of A C := 
  Refinement (@implem_composeK _ _ _ rab rbc).

(* Definition refines_trans A B C a b c *)
(*   `{refinement_of B C, refinement_of A B, !refines a b, !refines b c} : refines a c. *)
(* Proof. constructor. rewrite spec_refines /= spec_refines. Qed. *)

(* Instance implem_default A B `{Implem A B} (a : A) :  a (\implem_B%C a) | 999. *)
(* Proof. done. Qed. *)

Section Operations.

(* zero_op arity operations, i.e. constants *)
Class zero B := zero_op : B.
Local Notation "0" := zero_op : computable_scope.

Class one B := one_op : B.
Local Notation "1" := one_op : computable_scope.

(* Unary operations *)
Class opp B := opp_op : B -> B.
Local Notation "-%C" := opp_op.
Local Notation "- x" := (opp_op x) : computable_scope.

Class inv B := inv_op : B -> B.
Local Notation "x ^-1" := (inv_op x) : computable_scope.

(* Binary operations *)
Class add B := add_op : B -> B -> B.
Local Notation "+%C" := add_op.
Local Notation "x + y" := (add_op x y) : computable_scope.

Class sub B := sub_op : B -> B -> B.
Local Notation "x - y" := (sub_op x y) : computable_scope.

Class exp A B := exp_op : A -> B -> A.
Local Notation "x ^ y" := (exp_op x y) : computable_scope.

Class mul B := mul_op : B -> B -> B.
Local Notation "*%C" := mul_op.
Local Notation "x * y" := (mul_op x y) : computable_scope.

Class div B := div_op : B -> B -> B.
Local Notation "x / y" := (div_op x y) : computable_scope.

(* Comparisons *)
Class eq B := eq_op : B -> B -> bool.
Local Notation "x == y" := (eq_op x y) : computable_scope.

Class lt B := lt_op : B -> B -> bool.
Local Notation "x < y" := (lt_op x y) : computable_scope.

Class leq B := leq_op : B -> B -> bool.
Local Notation "x <= y" := (leq_op x y) : computable_scope.

Class gt B := gt_op : B -> B -> bool.
Local Notation "x > y" := (gt_op x y) : computable_scope.

Class geq B := geq_op : B -> B -> bool.
Local Notation "x >= y" := (geq_op x y) : computable_scope.

End Operations.

Notation "0"      := zero_op       : computable_scope.
Notation "1"      := one_op        : computable_scope.
Notation "-%C"    := opp_op.
Notation "- x"    := (opp_op x)    : computable_scope.
Notation "x ^-1"  := (inv_op x)    : computable_scope.
Notation "+%C"    := add_op.
Notation "x + y"  := (add_op x y)     : computable_scope.
Notation "x - y"  := (sub_op x y)     : computable_scope.
Notation "x ^ y"  := (exp_op x y)  : computable_scope.
Notation "*%C"    := mul_op.
Notation "x * y"  := (mul_op x y)  : computable_scope.
Notation "x / y"  := (div_op x y)  : computable_scope.
Notation "x == y" := (eq_op x y)   : computable_scope.
Notation "x < y " := (lt_op x y)   : computable_scope.
Notation "x <= y" := (leq_op x y)  : computable_scope.
Notation "x > y"  := (gt_op x y)   : computable_scope.
Notation "x >= y" := (geq_op x y)  : computable_scope.