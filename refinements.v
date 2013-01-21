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
Reserved Notation "\refines_ r a b" 
         (at level 0, format "\refines_ r  a  b",
          r at level 0, a at next level).

Delimit Scope computable_scope with C.

Local Open Scope ring_scope.

Import GRing.Theory.

Class refinement A B := Refinement {
  implem : A -> B;
  spec : B -> option A;
  implemK : pcancel implem spec
}.
Notation "\implem_ B" := (@implem _ B _) : computable_scope.
Notation "\implem" := (@implem _ _ _) (only parsing) : computable_scope.
Notation "\spec_ A" := (@spec A _ _) : computable_scope.
Notation "\spec" := (@spec _ _ _) (only parsing) : computable_scope.

Lemma implem_inj A B `{refinement A B} : injective implem.
Proof. exact: (pcan_inj implemK). Qed.

Definition specd A B `{refinement A B} (a : A) (b : B) := odflt a (spec b).

Lemma implem_composeK A B C `{refinement A B, refinement B C} :
  pcancel (\implem_C \o \implem_B)%C (obind \spec_A \o \spec_B)%C.
Proof. by move=> a /=; rewrite implemK /= implemK. Qed.

Definition refinement_id A : refinement A A := 
  Refinement (fun _ => erefl).

Class is_some {A : Type} (a : A) (b : option A) := is_someE : Some a = b.

Notation refines a b := (is_some a (spec b)).
Notation "\refines_ r a b" := (is_some a (@spec _ _ r b)) (only parsing).

Lemma spec_refines A B `{refinement A B} (a : A) (b : B) `{refines a b}:
  spec b = Some a.
Proof. by rewrite is_someE. Qed.

Lemma specd_refines A B `{refinement A B} (a : A) (b : B) `{refines a b}: 
  specd a b = a.
Proof. by rewrite /specd spec_refines. Qed.

Global Instance refinement_bool : refinement bool bool := refinement_id bool.
(* Global Instance refines_bool (a : bool) : refines a a := erefl. *)

Section local_trans.
Instance refinement_trans A B C
  (rab : refinement A B) (rbc : refinement B C) : refinement A C := 
  Refinement (@implem_composeK _ _ _ rab rbc).

Lemma refines_trans A B C
  (rab : refinement A B) (rbc : refinement B C)
  (a : A) (b : B) (c : C) `{!refines a b, !refines b c} :
  refines a c.
Proof. by do? rewrite /= spec_refines. Qed.
(* rac := refinement_trans rab rbc and leaving it implicit in the *)
(* conclusion leads to a Bad implicit argument number: 11 *)
End local_trans.

Class refines_step {A B} `{refinement A B} (a : A) (b : B) :=
  spec_refines_step : spec b = Some a.

Instance refines_step_refines {A B} `{refinement A B} {a : A} {b : B} :
  refines_step a b -> refines a b.
Proof. done. Qed.

(* We should use instead a "container datatype" library *)
(* where container T -> forall A B, refinement (T A) (T B) *)
Module parametric_pair.
Section parametric_pair.

Variables (A A' B B' : Type).
Context `{refinement A A'} `{refinement B B'}.

Definition ABtoAB' (ab : A * B) : (A' * B') := (implem ab.1, implem ab.2).
Definition AB'toAB (ab : A' * B') : option (A * B) :=
  obind (fun x => obind (fun y => Some (x, y)) (spec ab.2)) (spec ab.1).
Lemma ABtoAB'K : pcancel ABtoAB' AB'toAB.
Proof. by case=> x y; rewrite /ABtoAB' /AB'toAB !implemK. Qed.

Instance Qrefinement :
  refinement (A * B) (A' * B') :=  Refinement ABtoAB'K.

Instance refines_pair (a : A) (a' : A') (b : B) (b' : B') 
  `{refines a a'} `{refines b b'} : refines  (a, b) (a', b').
Proof. by rewrite /= /AB'toAB /= !spec_refines. Qed.

Instance refines_fst (ab : A * B) (ab' : A' * B'):
  refines ab ab' -> refines ab.1 ab'.1.
Proof.
by rewrite /= /AB'toAB; move: (spec _.1) (spec _.2) => [a|//] [b|//] [->].
Qed.

Instance refines_snd (ab : A * B) (ab' : A' * B'):
  refines ab ab' -> refines ab.2 ab'.2.
Proof.
by rewrite /= /AB'toAB; move: (spec _.1) (spec _.2) => [a|//] [b|//] [->].
Qed.

End parametric_pair.
Existing Instance Qrefinement.
Existing Instance refines_pair.
Existing Instance refines_fst.
Existing Instance refines_snd.

End parametric_pair.

Lemma refines_boolE (b b' : bool) {rb : refines b b'} : b = b'.
Proof. by move: b b' rb (@spec_refines _ _ _ _ _ rb) => [] []. Qed.

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
(* This is wrong! eq_op is taken *) 
Class eq B := eq_op : B -> B -> bool.
Local Notation "x == y" := (eq_op x y) : computable_scope.

Class lt B := lt_op : B -> B -> bool.
Local Notation "x < y" := (lt_op x y) : computable_scope.

Class leq B := leq_op : B -> B -> bool.
Local Notation "x <= y" := (leq_op x y) : computable_scope.

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
Notation "x > y"  := (lt_op y x)  (only parsing) : computable_scope.
Notation "x >= y" := (leq_op y x) (only parsing) : computable_scope.

