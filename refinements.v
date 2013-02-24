(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop ssrnum ssrint.

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

(* This class describe what is a type refinement *)
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

(* This class describes what is a term refinement *)
Class refines {A B} `{refinement A B} (a : A) (b : B) :=
  spec_refines_def : Some a = spec b.

Lemma spec_refines A B `{refinement A B} (a : A) (b : B)
      `{!refines a b} :  spec b = Some a.
Proof. by rewrite spec_refines_def. Qed.

Lemma specd_refines A B `{refinement A B} (a a0 : A) (b : B) `{!refines a b}: 
  specd a0 b = a.
Proof. by rewrite /specd spec_refines. Qed.

Global Instance refinement_bool : refinement bool bool := refinement_id bool.

Lemma refines_boolE (b b' : bool) {rb : refines b b'} : b = b'.
Proof. by move: b b' rb (@spec_refines _ _ _ _ _ rb) => [] []. Qed.

Lemma refinesP {A B} `{refinement A B}  (x y : A) (a : B) :
  refines x a -> (x = y <-> refines y a).
Proof. by move=> ra; split => [<- //|]; rewrite /refines -ra => [[->]]. Qed.

Section local_trans.
Instance refinement_trans A B C
  (rab : refinement A B) (rbc : refinement B C) : refinement A C := 
  Refinement (@implem_composeK _ _ _ rab rbc).

Lemma refines_trans A B C
  (rab : refinement A B) (rbc : refinement B C)
  (a : A) (b : B) (c : C) `{!refines a b, !refines b c} :
  refines a c.
Proof. by do? rewrite /refines /= spec_refines. Qed.
(* rac := refinement_trans rab rbc and leaving it implicit in the *)
(* conclusion leads to a Bad implicit argument number: 11 *)

Lemma refines_split A B C
  (rab : refinement A B) (rbc : refinement B C)
  (a : A) (c : C) : refines a c ->
  {b : B | (refines a b * refines b c)%type}.
Proof. by rewrite /refines /=; case: (spec c) => //= b; exists b. Qed.

Definition refines_split_wit A B C
  (rab : refinement A B) (rbc : refinement B C)
  (a : A) (c : C) (ra : refines a c) : B := projT1 (refines_split ra).

Lemma refines_split1 A B C
  (rab : refinement A B) (rbc : refinement B C)
  (a : A) (c : C) (ra : refines a c) : refines a (refines_split_wit ra).
Proof. by rewrite /refines_split_wit; case: (refines_split _) => ? []. Qed.

Lemma refines_split2 A B C
  (rab : refinement A B) (rbc : refinement B C)
  (a : A) (c : C) (ra : refines a c) : refines (refines_split_wit ra) c.
Proof. by rewrite /refines_split_wit; case: (refines_split _) => ? []. Qed.

End local_trans.

(* refines_step is a copy of refines, in order to ensure the termination *)
(* of proof search *)

Class refines_step {A B} `{refinement A B} (a : A) (b : B) :=
  spec_refines_step_def : Some a = spec b.

Lemma spec_refines_step A B `{refinement A B} (a : A) (b : B)
      `{!refines_step a b} :  spec b = Some a.
Proof. by rewrite spec_refines_step_def. Qed.

Definition refines_step_refines {A B} `{refinement A B} {a : A} {b : B} :
  refines_step a b -> refines a b.
Proof. done. Qed.


(* We take avantage of parametricity in a very ad-hoc way, for now *)
(* We should use instead a "container datatype" library *)
(* where container T -> forall A B, refinement (T A) (T B) *)
Module parametricity.
Section parametricity.

Variables (A A' B B' : Type).
Context `{refinement A A'} `{refinement B B'}.

Definition ABtoAB' (ab : A * B) : (A' * B') := (implem ab.1, implem ab.2).
Definition AB'toAB (ab : A' * B') : option (A * B) :=
  obind (fun x => obind (fun y => Some (x, y)) (spec ab.2)) (spec ab.1).
Lemma ABtoAB'K : pcancel ABtoAB' AB'toAB.
Proof. by case=> x y; rewrite /ABtoAB' /AB'toAB !implemK. Qed.

Instance pair_refinement :
  refinement (A * B) (A' * B') :=  Refinement ABtoAB'K.

Instance refines_pair (a : A) (a' : A') (b : B) (b' : B') 
  `{!refines a a'} `{!refines b b'} : refines  (a, b) (a', b').
Proof. by rewrite /refines /= /AB'toAB /= !spec_refines. Qed.

Instance refines_fst (ab : A * B) (ab' : A' * B'):
  refines ab ab' -> refines ab.1 ab'.1.
Proof.
rewrite /refines /= /AB'toAB.
by move: (spec _.1) (spec _.2) => [a|//] [b|//] [->].
Qed.

Instance refines_snd (ab : A * B) (ab' : A' * B'):
  refines ab ab' -> refines ab.2 ab'.2.
Proof.
rewrite /refines /= /AB'toAB.
by move: (spec _.1) (spec _.2) => [a|//] [b|//] [->].
Qed.

Instance refines_if 
         (c : bool) (c' : bool) (a : A) (a' : A') (b : A) (b' : A') 
   {rc : refines c c'}  `{!refines a a'} `{!refines b b'} :
  refines (if c then a else b) (if c' then a' else b').
Proof. by rewrite [c]refines_boolE; case: c' rc. Qed.

End parametricity.
Existing Instance pair_refinement.
Existing Instance refines_pair.
Existing Instance refines_fst.
Existing Instance refines_snd.
Existing Instance refines_if.

End parametricity.

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

Class embed_class A B := embed_op : A -> B.
Global Instance id_embed A : embed_class A A := id.

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
Notation embed := (@embed_op _).

Ltac simpC :=
  do ?[ rewrite -[0%C]/0%R | rewrite -[1%C]/1%R
      | rewrite -[(_ + _)%C]/(_ + _)%R
      | rewrite -[(_ + _)%C]/(_ + _)%N
      | rewrite -[(- _)%C]/(- _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%R
      | rewrite -[(_ * _)%C]/(_ * _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%N
      | rewrite -[(_ * _)%C]/(_ * _)%N
      | rewrite -[(_ / _)%C]/(_ / _)%R
      | rewrite -[(_ == _)%C]/(_ == _)%bool
      | rewrite -[(_ <= _)%C]/(_ <= _)%R
      | rewrite -[(_ < _)%C]/(_ < _)%R
      | rewrite -[(_ <= _)%C]/(_ <= _)%N
      | rewrite -[(_ < _)%C]/(_ < _)%N
      | rewrite -[embed _]/(_%:R)
      | rewrite -[embed _]/(_%:~R)].

(* Opacity of ssr symbols *)
Typeclasses Opaque eqtype.eq_op.
Typeclasses Opaque GRing.zero.
Typeclasses Opaque GRing.add.
Typeclasses Opaque GRing.opp.
Typeclasses Opaque GRing.one.
Typeclasses Opaque GRing.mul.
Typeclasses Opaque GRing.inv.
Typeclasses Opaque Num.le.
Typeclasses Opaque Num.lt.
Typeclasses Opaque Num.norm.
