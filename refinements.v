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

Ltac tc := do 1?typeclasses eauto.

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

Notation refines_id := (@refines _ _ (@refinement_id _)).
Notation "@refines_id A" := (@refines A A (@refinement_id _))
  (at level 10).

(*****************)
(* PARAMETRICITY *)
(*****************)

Definition respectful_gen {A B C D : Type}
  (R : A -> B -> Prop) (R' : C -> D -> Prop) : (A -> C) -> (B -> D) -> Prop :=
  Classes.Morphisms.respectful_hetero _ _ _ _ R (fun x y => R').

Arguments respectful_gen {A B C D}
  R%computable_scope R'%computable_scope _ _.
Notation " R ==> S " := (@respectful_gen _ _ _ _ R S)
    (right associativity, at level 55) : computable_scope.

Fact getparam_key : unit. Proof. done. Qed.
Fact    param_key : unit. Proof. done. Qed.

Class param A B (R : A -> B -> Prop) (m : A) (n : B) := 
  param_rel : (locked_with param_key R) m n.
Arguments param {A B} R%computable_scope m n.

Class getparam {A B} (R : A -> B -> Prop) (m : A) (n : B) := 
  getparam_rel : (locked_with getparam_key R) m n.
Arguments getparam {A B} R%computable_scope m n.

Lemma paramE A B (R : A -> B -> Prop) : (param R = R) * (getparam R = R).
Proof. by rewrite /param /getparam !unlock. Qed.

Lemma param_refl A (a : A) :
  getparam (@refines _ _ (@refinement_id A)) a a.
Proof. by rewrite paramE. Qed.
Global Hint Extern 0 (getparam _ _ _)
  => now eapply @param_refl : typeclass_instances.

Global Instance param_apply A B C D
 (R : A -> B -> Prop) (R' : C -> D -> Prop)
 (a :  A) (b : B) (c : A -> C) (d : B -> D):
  param (R ==> R') c d ->
  getparam R a b -> param R' (c a) (d b) | 1.
Proof. by rewrite !paramE => rcd rab; apply rcd. Qed.

Global Instance param_id (T T' : Type) (R : T -> T' -> Prop) :
   param (R ==> R) id id.
Proof. by rewrite paramE. Qed.

Lemma id_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  param R x y -> param R x y.
Proof. done. Qed.

Lemma get_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
   getparam R x y -> param R x y.
Proof. by rewrite !paramE. Qed.

Lemma set_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  param R x y -> getparam R x y.
Proof. by rewrite !paramE. Qed.
Global Hint Extern 999 (getparam refines _ _)
 => eapply set_param : typeclass_instances.

Class composable A B C
 (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) (rAC : A -> C -> Prop) : Type :=
  composable_trans : forall b a c, rAB a b -> rBC b c -> rAC a c.
Arguments composable {A B C} rAB%computable_scope
  rBC%computable_scope rAC%computable_scope.

Section local_trans.
Local Instance refinement_trans A B C
  (rab : refinement A B) (rbc : refinement B C) : refinement A C := 
  Refinement (@implem_composeK _ _ _ rab rbc).

Lemma refines_trans A B C (rab : refinement A B) (rbc : refinement B C)
  (a : A) (b : B) (c : C) `{!refines a b, !refines b c} : refines a c.
Proof. by do? rewrite /refines /= spec_refines. Qed.
(* rac := refinement_trans rab rbc and leaving it implicit in the *)
(* conclusion leads to a Bad implicit argument number: 11 *)

Lemma refines_split A B C
  (rab : refinement A B) (rbc : refinement B C)
  (a : A) (c : C) : refines a c ->
  {b : B | (refines a b * refines b c)%type}.
Proof. by rewrite /refines /=; case: (spec c) => //= b; exists b. Qed.

Lemma param_trans A B C
  (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) (rAC : A -> C -> Prop)
  (a : A) (b : B) (c : C) :
  composable rAB rBC rAC ->
  getparam rAB a b -> getparam rBC b c -> param rAC a c.
Proof.
by rewrite !paramE => cABC rab rbc; apply: composable_trans rab rbc.
Qed.

Lemma composable_rid1 A B (R : A -> B -> Prop):
  composable R refines_id R.
Proof. by move=> b a c rab [<-]. Qed.

Lemma composable_refines A B C
  (rAB : refinement A B) (rBC : refinement B C) :
  composable (@refines A B _) (@refines B C _) refines.
Proof. by move=> b a c; eapply @refines_trans. Qed.

Lemma composable_imply_id1 A B A' B' C'
  (rAB : refinement A B)
  (R1 : A' -> B' -> Prop) (R2 : B' -> C' -> Prop) (R3 : A' -> C' -> Prop):
composable R1 R2 R3 ->
composable (refines_id ==> R1)
           (@refines A B _  ==> R2) (refines ==> R3).
Proof.
move=> cR b a c rab rbc x z rxz /=.
exact: (composable_trans (rab x x erefl) (rbc x z rxz)).
Qed.

(* Lemma composable_imply_id2 A A' B' C' *)
(*   (R1 : A' -> B' -> Prop) (R2 : B' -> C' -> Prop) (R3 : A' -> C' -> Prop): *)
(* composable R1 R2 R3 -> *)
(* composable (refines_id ==> R1) *)
(*            (refines_id ==> R2) (@refines_id A ==> R3). *)
(* Proof. *)
(* move=> cR b a c rab rbc x z rxz /=. *)
(* exact: (composable_trans (rab x z rxz) (rbc z z erefl)). *)
(* Qed. *)

Lemma composable_imply A B C A' B' C'
  (rAB : refinement A B) (rBC : refinement B C)
  (R1 : A' -> B' -> Prop) (R2 : B' -> C' -> Prop) (R3 : A' -> C' -> Prop):
composable R1 R2 R3 ->
composable (@refines A B _ ==> R1)
           (@refines B C _ ==> R2) (refines ==> R3).
Proof.
move=> cR b a c rab rbc x z rxz /=.
have [y [rxy ryz]] := (refines_split rxz).
exact: (composable_trans (rab x y rxy) (rbc y z ryz)).
Qed.

End local_trans.

(* refines_step is a copy of refines, in order to ensure the termination *)
(* of proof search *)

Instance param_refines A B (rAB : refinement A B) (a : A) (b : B)
  (rab : param refines a b) : refines a b.
Proof. by rewrite paramE in rab. Qed.

Hint Extern 0 (composable _ _ refines)
 => now eapply composable_refines : typeclass_instances.

Hint Extern 1 (composable _ _ refines)
 => now eapply @composable_rid1 : typeclass_instances.

Hint Extern 2 (composable _ _ (_ ==> _))
 => eapply composable_imply : typeclass_instances.

Hint Extern 3 (composable _ _ (_ ==> _))
 => eapply composable_imply_id1 : typeclass_instances.

(* We take avantage of parametricity in a very ad-hoc way, for now *)
(* We could use instead a "container datatype" library *)
(* where container T -> forall A B, refinement (T A) (T B) *)

Module Parametricity.
Section Parametricity.

Variables (A A' B B' : Type).
Context `{refinement A A'} `{refinement B B'}.

Definition ABtoAB' (ab : A * B) : (A' * B') := (implem ab.1, implem ab.2).
Definition AB'toAB (ab : A' * B') : option (A * B) :=
  obind (fun x => obind (fun y => Some (x, y)) (spec ab.2)) (spec ab.1).
Lemma ABtoAB'K : pcancel ABtoAB' AB'toAB.
Proof. by case=> x y; rewrite /ABtoAB' /AB'toAB !implemK. Qed.

Definition pair_refinement : refinement (A * B) (A' * B') := Refinement ABtoAB'K.

Hint Extern 1 (@refinement (_ * _) (_ * _)) =>
  eapply pair_refinement : typeclass_instances.

Instance param_pair :
  param (refines ==> refines ==> refines) (@pair A B) (@pair A' B').
Proof.
rewrite !paramE => a a' ra b b' br.
by rewrite /refines /= /AB'toAB /= !spec_refines.
Qed.

Instance param_fst : param (refines ==> refines) (@fst A B) (@fst A' B').
Proof.
rewrite !paramE => ab ab'; rewrite /refines /= /AB'toAB.
by move: (spec _.1) (spec _.2) => [a|//] [b|//] [->].
Qed.

Instance param_snd : param (refines ==> refines) (@snd A B) (@snd A' B').
Proof.
rewrite !paramE => ab ab'; rewrite /refines /= /AB'toAB.
by move: (spec _.1) (spec _.2) => [a|//] [b|//] [->].
Qed.

Instance param_if 
         (c : bool) (c' : bool) (a : A) (a' : A') (b : A) (b' : A') 
   {rc : param refines c c'}  `{!param refines a a'} `{!param refines b b'} :
  param refines (if c then a else b) (if c' then a' else b').
Proof. Admitted.

End Parametricity.

Lemma param_abstr A B C D (R : A -> B -> Prop) (R' : C -> D -> Prop)
      (c : A -> C) (d : B -> D):
        (forall (a :  A) (b : B), param R a b -> getparam R' (c a) (d b)) ->
        getparam (R ==> R') c d.
Proof. by rewrite !paramE; apply. Qed.

Global Hint Extern 2 (getparam (_ ==> _) _ _)
 => eapply @param_abstr=>??? : typeclass_instances.

Lemma param_abstr2 A B A' B' A'' B'' 
      (R : A -> B -> Prop) (R' : A' -> B' -> Prop) (R'' : A'' -> B'' -> Prop)
      (f : A -> A' -> A'' ) (g : B -> B' -> B''):
        (forall (a : A) (b : B) (a' : A') (b' : B'),
           param R a b -> param R' a' b' -> getparam R'' (f a a') (g b b')) ->
        getparam (R ==> R' ==> R'') f g.
Proof. by tc. Qed.

Global Hint Extern 1 (getparam (_ ==> _ ==> _) _ _)
 => eapply @param_abstr2=> ??? ??? : typeclass_instances.

Hint Extern 1 (@refinement _ (_ * _)) =>
  eapply pair_refinement : typeclass_instances.

Hint Extern 1 (@refinement (_ * _) _) =>
  eapply pair_refinement : typeclass_instances.

Existing Instance param_if.
Existing Instance param_pair.
Existing Instance param_fst.
Existing Instance param_snd.

End Parametricity.

Definition unfold A := @id A.
Typeclasses Opaque unfold.

Global Instance set_param_pair X A
  (R : X -> A -> Prop) (x : X) (a : A) :
 param R x a -> param R (unfold x) (unfold a). 
Proof. by []. Qed.

Module Refinements.

Module Op.

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

Class scale A B := scale_op : A -> B -> B.
Local Notation "x *: y" := (scale_op x y) : computable_scope.

Class div B := div_op : B -> B -> B.
Local Notation "x / y" := (div_op x y) : computable_scope.

(* Comparisons *)
Class eq B := eq_op : B -> B -> bool.
Local Notation "x == y" := (eq_op x y) : computable_scope.

Class lt B := lt_op : B -> B -> bool.
Local Notation "x < y" := (lt_op x y) : computable_scope.

Class leq B := leq_op : B -> B -> bool.
Local Notation "x <= y" := (leq_op x y) : computable_scope.

Class cast_class A B := cast_op : A -> B.
Global Instance id_cast A : cast_class A A := id.

Class dvd B := dvd_op : B -> B -> bool.
Local Notation "x %| y" := (dvd_op x y) : computable_scope.

End Op.

End Refinements.

Definition subr {R : zmodType} (x y : R) := x - y.
Definition divr {R : unitRingType} (x y : R) := x / y.

Import Refinements.Op.

Notation "0"      := zero_op        : computable_scope.
Notation "1"      := one_op         : computable_scope.
Notation "-%C"    := opp_op.
Notation "- x"    := (opp_op x)     : computable_scope.
Notation "x ^-1"  := (inv_op x)     : computable_scope.
Notation "+%C"    := add_op.
Notation "x + y"  := (add_op x y)   : computable_scope.
Notation "x - y"  := (sub_op x y)   : computable_scope.
Notation "x ^ y"  := (exp_op x y)   : computable_scope.
Notation "*%C"    := mul_op.
Notation "x * y"  := (mul_op x y)   : computable_scope.
Notation "x *: y" := (scale_op x y) : computable_scope.
Notation "x / y"  := (div_op x y)   : computable_scope.
Notation "x == y" := (eq_op x y)    : computable_scope.
Notation "x < y " := (lt_op x y)    : computable_scope.
Notation "x <= y" := (leq_op x y)   : computable_scope.
Notation "x > y"  := (lt_op y x)  (only parsing) : computable_scope.
Notation "x >= y" := (leq_op y x) (only parsing) : computable_scope.
Notation cast := (@cast_op _).
Notation "x %| y" := (dvd_op x y)   : computable_scope.

Ltac simpC :=
  do ?[ rewrite -[0%C]/0%R | rewrite -[1%C]/1%R
      | rewrite -[(_ + _)%C]/(_ + _)%R
      | rewrite -[(_ + _)%C]/(_ + _)%N
      | rewrite -[(- _)%C]/(- _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%N
      | rewrite -[(_ * _)%C]/(_ * _)%R
      | rewrite -[(_ * _)%C]/(_ * _)%N
      | rewrite -[(_ *: _)%C]/(_ *: _)%R
      | rewrite -[(_ / _)%C]/(_ / _)%R
      | rewrite -[(_ == _)%C]/(_ == _)%bool
      | rewrite -[(_ <= _)%C]/(_ <= _)%R
      | rewrite -[(_ < _)%C]/(_ < _)%R
      | rewrite -[(_ <= _)%C]/(_ <= _)%N
      | rewrite -[(_ < _)%C]/(_ < _)%N
      | rewrite -[cast _]/(_%:R)
      | rewrite -[cast _]/(_%:~R)].

(* Opacity of ssr symbols *)
Typeclasses Opaque eqtype.eq_op.
Typeclasses Opaque addn subn muln expn.
Typeclasses Opaque GRing.zero GRing.add GRing.opp GRing.natmul.
Typeclasses Opaque GRing.one GRing.mul GRing.inv GRing.exp GRing.scale.
Typeclasses Opaque subr divr.
Typeclasses Opaque Num.le Num.lt Num.norm.
Typeclasses Opaque intmul exprz absz.

Typeclasses Transparent zero one add opp sub.
Typeclasses Transparent mul exp inv div scale.
Typeclasses Transparent eq lt leq cast_class.
