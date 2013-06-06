(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop ssrnum ssrint matrix.

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
Delimit Scope hetero_computable_scope with HC.
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

(*****************)
(* PARAMETRICITY *)
(*****************)
Fact getparam_key : unit. Proof. done. Qed.

Class param {A B} (R : A -> B -> Prop) (m : A) (n : B) := 
  param_rel : R m n.
Arguments param {A B} R%rel_scope m n.

Class getparam {A B} (R : A -> B -> Prop) (m : A) (n : B) := 
  getparam_rel : (locked_with getparam_key R) m n.
Arguments getparam {A B} R%rel_scope m n.

Lemma paramE A B (R : A -> B -> Prop) : (param R = R) * (getparam R = R).
Proof. by rewrite /param /getparam !unlock. Qed.

Global Instance param_sub_proper {A B} :
   Proper (sub_hrel ==> eq ==> eq ==> impl) (@param A B).
Proof. by move=> R S RS x _ <- y _ <-; move: x y; rewrite !paramE. Qed.

Global Instance param_proper {A B} :
   Proper (eq_hrel ==> eq ==> eq ==> iff) (@param A B).
Proof. by move=> ?? [??] ??? ???; split; apply: param_sub_proper. Qed.

Global Instance getparam_proper {A B} :
   Proper (eq_hrel ==> eq ==> eq ==> iff) (@getparam A B).
Proof. by move=> *; rewrite !paramE; apply: param_proper. Qed.

Lemma getparam_refl A (a : A) : getparam eq a a.
Proof. by rewrite paramE. Qed.
Global Hint Extern 0 (getparam _ _ _)
  => now eapply @getparam_refl : typeclass_instances.

Global Instance param_apply A B C D
 (R : A -> B -> Prop) (R' : C -> D -> Prop)
 (a :  A) (b : B) (c : A -> C) (d : B -> D):
  param (R ==> R') c d -> param R a b -> param R' (c a) (d b) | 1.
Proof. by move=> rcd rab; apply rcd. Qed.

Global Instance param_id (T T' : Type) (R : T -> T' -> Prop) :
   param (R ==> R) id id.
Proof. done. Qed.

Lemma id_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  param R x y -> param R x y.
Proof. done. Qed.

Global Instance trivial_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  R x y -> param R x y.
Proof. done. Qed.

Lemma get_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
   getparam R x y -> param R x y.
Proof. by rewrite !paramE. Qed.

Lemma set_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  param R x y -> getparam R x y.
Proof. by rewrite !paramE. Qed.
(* Global Hint Extern 999 (getparam refines _ _) *)
(*  => eapply set_param : typeclass_instances. *)

Class composable {A B C}
 (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) (rAC : A -> C -> Prop) := 
  Composable : (rAB \o rBC <= rAC)%rel.
Arguments composable {A B C} rAB%rel rBC%rel rAC%rel.

Global Instance composable_sub_proper {A B C} :
   Proper (sub_hrel --> sub_hrel --> sub_hrel ==> impl) (@composable A B C).
Proof. 
rewrite /composable => R S RS T U TU V W VW RTV.
by setoid_rewrite <- RS; setoid_rewrite <- TU; setoid_rewrite <- VW.
Qed.

Global Instance composable_proper {A B C} :
   Proper (eq_hrel ==> eq_hrel ==> eq_hrel ==> iff) (@composable A B C).
Proof.
by move=> ?? [??] ?? [??] ?? [??]; split; apply: composable_sub_proper.
Qed.

Lemma param_trans A B C
  (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) (rAC : A -> C -> Prop)
  (a : A) (b : B) (c : C) :
  param rAB a b ->  composable rAB rBC rAC ->
  getparam rBC b c -> param rAC a c.
Proof. by rewrite !paramE => rab rABC rbc; apply: rABC; exists b. Qed.

(* Local Instance refinement_trans A B C *)
(*   (rab : refinement A B) (rbc : refinement B C) : refinement A C :=  *)
(*   Refinement (@implem_composeK _ _ _ rab rbc). *)

(* Lemma refines_trans A B C (rab : refinement A B) (rbc : refinement B C) *)
(*   (a : A) (b : B) (c : C) `{!refines a b, !refines b c} : refines a c. *)
(* Proof. by do? rewrite /refines /= spec_refines. Qed. *)
(* (* rac := refinement_trans rab rbc and leaving it implicit in the *) *)
(* (* conclusion leads to a Bad implicit argument number: 11 *) *)

Lemma composable_rid1 A B (R : A -> B -> Prop): composable eq R R.
Proof. by rewrite /composable comp_eql. Qed.

Lemma composable_comp A B C (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) :
  composable rAB rBC (rAB \o rBC)%rel.
Proof. done. Qed.

Lemma composable_imply {A B C A' B' C'}
  (rAB : A -> B -> Prop) (rBC : B -> C -> Prop)
  (R1 : A' -> B' -> Prop) (R2 : B' -> C' -> Prop) (R3 : A' -> C' -> Prop):
composable R1 R2 R3 -> composable (rAB ==> R1) (rBC ==> R2) (rAB \o rBC ==> R3).
Proof.
rewrite /composable => R123.
transitivity (rAB \o rBC ==> R1 \o R2)%rel; last exact: hrespectful_sub_proper.
move=> f h [g []] Rfg Rgh x z [y [rxy ryz]]; exists (g y).
by split; [apply: Rfg|apply: Rgh].
Qed.

Lemma composable_imply_id1 {A B A' B' C'}
  (rAB : A -> B -> Prop)
  (R1 : A' -> B' -> Prop) (R2 : B' -> C' -> Prop) (R3 : A' -> C' -> Prop):
composable R1 R2 R3 -> composable (eq ==> R1) (rAB ==> R2) (rAB ==> R3).
Proof. by rewrite -[X in (X ==> R3)%rel]comp_eql; apply: composable_imply. Qed.

Lemma paramR A B (R : A -> B -> Prop) (a : A) (b : B)
  (rab : param R a b) : R a b.
Proof. by rewrite paramE in rab. Qed.

(* Hint Extern 0 (refines _ _) => eapply paramR : typeclass_instances. *)

Hint Extern 0 (composable _ _ (_ \o _))
 => now eapply composable_comp : typeclass_instances.

Hint Extern 1 (composable _ _ _)
 => now eapply @composable_rid1 : typeclass_instances.

Hint Extern 2 (composable _ _ (_ ==> _))
 => eapply composable_imply : typeclass_instances.

Hint Extern 3 (composable _ _ (_ ==> _))
 => eapply composable_imply_id1 : typeclass_instances.

(* We take avantage of parametricity in a very ad-hoc way, for now *)
(* We could use instead a "container datatype" library *)
(* where container T -> forall A B, refinement (T A) (T B) *)

Section Parametricity.

Local Open Scope ring_scope.

Import GRing.Theory.

(* This class describe what is a type refinement *)
Class refinement {A B} (R : A -> B -> Prop) := Refinement {
  implem : A -> B;
  spec : B -> option A;
  implemK : pcancel implem spec;
  refinementP : ((fun x y => spec y = Some x) <=> R)%rel
}.
Notation "\implem_ B" := (@implem _ B _ _) : computable_scope.
Notation "\implem" := (@implem _ _ _ _) (only parsing) : computable_scope.
Notation "\spec_ A" := (@spec A _ _ _) : computable_scope.
Notation "\spec" := (@spec _ _ _ _) (only parsing) : computable_scope.

Lemma implem_inj `{refinement} : injective implem.
Proof. exact: (pcan_inj implemK). Qed.

Definition specd A B `{refinement A B} (a : A) (b : B) := odflt a (spec b).

Lemma implem_composeK A B C rAB rBC `{refinement A B rAB, refinement B C rBC} :
  pcancel (\implem_C \o \implem_B)%C (obind \spec_A \o \spec_B)%C.
Proof. by move=> a /=; rewrite implemK /= implemK. Qed.

Program Definition refinement_id A : refinement (@eq A) :=
  Refinement (fun _ => erefl) _.
Next Obligation. by apply: EqHrel => [x y []|x y ->]. Qed.

(* This class describes what is a term refinement *)
Definition refines {A B R} `{refinement A B R} := R.

Lemma spec_refines A B R `{refinement A B R} (a : A) (b : B) :
  param R a b -> spec b = Some a.
Proof. by apply: eq_hrelLR refinementP _ _. Qed.

Global Instance refinement_bool : refinement (@eq bool) := refinement_id bool.

Lemma refines_boolE (b b' : bool) {rb : refines b b'} : b = b'.
Proof. by rewrite rb. Qed.

Lemma refinesP {A B} `{refinement A B}  (x y : A) (a : B) :
  param refines x a -> (param refines y a <-> x = y).
Proof. by rewrite -[refines]refinementP paramE => ->; split=> [[]|->]. Qed.

Lemma getparam_abstr A B C D (R : A -> B -> Prop) (R' : C -> D -> Prop)
      (c : A -> C) (d : B -> D):
        (forall (a :  A) (b : B), param R a b -> getparam R' (c a) (d b)) ->
        getparam (R ==> R') c d.
Proof. by rewrite !paramE; apply. Qed.

Hint Extern 2 (getparam (_ ==> _) _ _)
 => eapply @getparam_abstr=>??? : typeclass_instances.

Lemma getparam_abstr2 A B A' B' A'' B'' 
      (R : A -> B -> Prop) (R' : A' -> B' -> Prop) (R'' : A'' -> B'' -> Prop)
      (f : A -> A' -> A'' ) (g : B -> B' -> B''):
        (forall (a : A) (b : B) (a' : A') (b' : B'),
           param R a b -> param R' a' b' -> getparam R'' (f a a') (g b b')) ->
        getparam (R ==> R' ==> R'') f g.
Proof. by tc. Qed.

Hint Extern 1 (getparam (_ ==> _ ==> _) _ _)
 => eapply @getparam_abstr2=> ??? ??? : typeclass_instances.

Lemma param_abstr A B C D (R : A -> B -> Prop) (R' : C -> D -> Prop)
      (c : A -> C) (d : B -> D):
        (forall (a :  A) (b : B), param R a b -> param R' (c a) (d b)) ->
        param (R ==> R') c d.
Proof. by rewrite !paramE; apply. Qed.

Lemma param_abstr2 A B A' B' A'' B'' 
      (R : A -> B -> Prop) (R' : A' -> B' -> Prop) (R'' : A'' -> B'' -> Prop)
      (f : A -> A' -> A'' ) (g : B -> B' -> B''):
        (forall (a : A)   (b : B), param R a b ->
         forall (a' : A') (b' : B'), param R' a' b' ->
        param R'' (f a a') (g b b')) ->
        param (R ==> R' ==> R'') f g.
Proof. by move=> H; do 2![eapply param_abstr => *]; apply: H. Qed.

Definition unfold A := @id A.
Typeclasses Opaque unfold.

(* buggy *)
Lemma param_unfold X A
  (R : X -> A -> Prop) (x : X) (a : A) :
 param R x a -> getparam R (unfold x) (unfold a).
Proof. by rewrite !paramE. Qed.

End Parametricity.

Global Hint Extern 999 (getparam _ _ _)
 => apply set_param : typeclass_instances.

Hint Extern 2 (getparam (_ ==> _) _ _)
 => eapply @getparam_abstr=> ??? : typeclass_instances.

Hint Extern 1 (getparam (_ ==> _ ==> _) _ _)
 => eapply @getparam_abstr2=> ??? ??? : typeclass_instances.


Section prod.
Context {A A' B B' : Type} (rA : A -> A' -> Prop) (rB : B -> B' -> Prop).

Definition prod_hrel : A * B -> A' * B' -> Prop :=
  fun x y => param rA x.1 y.1 /\ param rB x.2 y.2.

Global Instance param_pair : param (rA ==> rB ==> prod_hrel) (@pair A B) (@pair A' B').
Proof. done. Qed.

Global Instance param_fst : param (prod_hrel ==> rA) (@fst _ _) (@fst _ _).
Proof. by move=> [??] [??] []. Qed.

Global Instance param_snd : param (prod_hrel ==> rB) (@snd _ _) (@snd _ _).
Proof. by move=> [??] [??] []. Qed.

Definition implem_prod (RA : refinement rA) (RB : refinement rB) (x : A * B) :=
  (implem x.1, implem x.2).
Definition spec_prod (RA : refinement rA) (RB : refinement rB) (x : A' * B') :=
  if (spec x.1, spec x.2) is (Some a, Some b) then Some (a, b) else None.

Program Definition refinement_prod (RA : refinement rA) (RB : refinement rB) :
  refinement prod_hrel := @Refinement _ _ _ (implem_prod RA RB) (spec_prod RA RB) _ _.
Next Obligation. by move=> [x y] /=; rewrite /spec_prod !implemK. Qed.
Next Obligation.
split=> [[??][??]|[??][??][]]; rewrite /prod_hrel /=;
rewrite -[rA]refinementP -[rB]refinementP !paramE /=;
rewrite /spec_prod; do 2![case: spec => // ?].
  by case=> -> ->.
by move=> [->] [->].
Qed.

End prod.
Arguments prod_hrel {_ _ _ _} rA%rel rB%rel _ _.
Notation "X * Y" := (prod_hrel X Y) : rel_scope.
Global Existing Instance refinement_prod.

Section param_seq.
Context {A B : Type} (rAB : A -> B -> Prop).

Fixpoint seq_hrel sa sb : Prop :=
  match sa, sb with
    | [::],    [::]    => True
    | a :: sa, b :: sb => rAB a b /\ seq_hrel sa sb
    | _,       _       => False
  end.

Global Instance param_nil : param seq_hrel nil nil. Proof. done. Qed.

Global Instance param_cons : param (rAB ==> seq_hrel ==> seq_hrel) cons cons.
Proof. done. Qed.

Definition seq_elim {X Y} (f0 : Y) (f_cons : X -> Y -> Y) :=
  fix f s := match s with [::] => f0 | x :: s => f_cons x (f s) end.

Global Instance param_seq_rect {C D : Type} (rCD : C -> D -> Prop) :
  param (rCD ==> (rAB ==> rCD ==> rCD) ==> seq_hrel ==> rCD) seq_elim seq_elim.
Proof. 
move=> c d rcd f g rfg; elim=> [|x s /= ihs] [|y t] // [rxy rst].
by apply: rfg => //; apply: ihs.
Qed.

End param_seq.

Global Instance param_if {A A'}
       (c : bool) (c' : bool) (a : A) (a' : A') (b : A) (b' : A') 
         (R : A -> A' -> Prop)
   {rc : param eq c c'}  `{!param R a a'} `{!param R b b'} :
  param R (if c then a else b) (if c' then a' else b').
Proof. by move: rc => [[<-]]; case: c. Qed.

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
Local Notation "*:%C" := scale_op.
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

(* Heterogeneous operations *)
(* Represent a pre-additive category *)
Class hzero {I} B := hzero_op : forall m n : I, B m n.
Local Notation "0" := hzero_op : hetero_computable_scope.

Class hone {I} B := hone_op : forall n : I, B n n.
Local Notation "!" := hone_op : hetero_computable_scope.

Class hadd {I} B := hadd_op : forall m n : I, B m n -> B m n -> B m n.
Local Notation "+%HC" := hadd_op.
Local Notation "x + y" := (add_op x y) : hetero_computable_scope.

Class hopp {I} B := hopp_op : forall m n : I, B m n -> B m n.
Local Notation "-%HC" := hopp_op.
Local Notation "- x" := (hopp_op x) : hetero_computable_scope.

Class hsub {I} B := hsub_op : forall m n : I, B m n -> B m n -> B m n.
Local Notation "x - y" := (sub_op x y) : hetero_computable_scope.

Class hinv {I} B := hinv_op : forall m n : I, B m n -> B m n.
Local Notation "x ^-1" := (hinv_op x) : hetero_computable_scope.

Class hmul {I} B := hmul_op : forall m n p : I, B m n -> B n p -> B m p.

Class heq {I} B := heq_op : forall m n : I, B m n -> B m n -> bool.
Local Notation "==%HC" := heq_op.
Local Notation "x == y" := (heq_op x y) : hetero_computable_scope.

Class hcast {I} B := hcast_op : forall m n m' n' : I,
  (m = m') * (n = n') -> B m n -> B m' n'.

(* Surgery on matrix-like data types *)
Local Open Scope nat_scope.
Class ulsub B := ulsubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n1.
Class ursub B := ursubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n2.
Class dlsub B := dlsubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n1.
Class drsub B := drsubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n2.
Class block B := block_mx : forall (m1 m2 n1 n2 : nat),
  B m1 n1 -> B m1 n2 -> B m2 n1 -> B m2 n2 -> B (m1 + m2) (n1 + n2).

End Op.

End Refinements.

Local Open Scope ring_scope.

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
Notation "*:%C"   := scale_op.
Notation "x / y"  := (div_op x y)   : computable_scope.
Notation "x == y" := (eq_op x y)    : computable_scope.
Notation "x < y " := (lt_op x y)    : computable_scope.
Notation "x <= y" := (leq_op x y)   : computable_scope.
Notation "x > y"  := (lt_op y x)  (only parsing) : computable_scope.
Notation "x >= y" := (leq_op y x) (only parsing) : computable_scope.
Notation cast := (@cast_op _).
Notation "x %| y" := (dvd_op x y)   : computable_scope.

Notation "0"      := hzero_op        : hetero_computable_scope.
Notation "1"      := hone_op         : hetero_computable_scope.
Notation "-%HC"    := hopp_op.
Notation "- x"    := (hopp_op x)     : hetero_computable_scope.
Notation "x ^-1"  := (hinv_op x)     : hetero_computable_scope.
Notation "+%HC"    := hadd_op.
Notation "x + y"  := (hadd_op x y)   : hetero_computable_scope.
Notation "x - y"  := (hsub_op x y)   : hetero_computable_scope.
Notation "x == y" := (heq_op x y)    : hetero_computable_scope.

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
      | rewrite -[cast _]/(_%:~R)
      | rewrite -[hzero_op _ _]/(const_mx 0)
      | rewrite -[hone_op _]/1%R
      | rewrite -[hadd_op _ _]/(addmx _ _)
      | rewrite -[hsub_op _ _]/(fun _ _ => addmx _ (oppmx _))
      | rewrite -[hmul_op _ _]/(mulmx _ _)
      | rewrite -[heq_op _ _]/(_ == _)%bool
      | rewrite -[hcast_op _ _]/(castmx _ _)
      | rewrite -[ulsub_op _]/(ulsubmx _)
      | rewrite -[ursub_op _]/(ursubmx _)
      | rewrite -[dlsub_op _]/(dlsubmx _)
      | rewrite -[drsub_op _]/(drsubmx _)
      | rewrite -[block_op _ _ _ _]/(block_mx _ _ _ _)].

(* Opacity of ssr symbols *)
Typeclasses Opaque eqtype.eq_op.
Typeclasses Opaque addn subn muln expn.
Typeclasses Opaque GRing.zero GRing.add GRing.opp GRing.natmul.
Typeclasses Opaque GRing.one GRing.mul GRing.inv GRing.exp GRing.scale.
Typeclasses Opaque Num.le Num.lt Num.norm.
Typeclasses Opaque intmul exprz absz.

Typeclasses Transparent zero one add opp sub.
Typeclasses Transparent mul exp inv div scale.
Typeclasses Transparent eq lt leq cast_class.

Module AlgOp.
Section AlgOp.

Definition subr {R : zmodType} (x y : R) := x - y.
Definition divr {R : unitRingType} (x y : R) := x / y.

End AlgOp.
End AlgOp.

Typeclasses Opaque AlgOp.subr AlgOp.divr.
