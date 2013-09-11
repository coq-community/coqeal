(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop ssrnum ssrint matrix.

(** This file implements the basic theory of refinements *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Reserved Notation "\implem_ A" (at level 0, format "\implem_ A"). *)
(* Reserved Notation "\implem" (at level 0, format "\implem"). *)
(* Reserved Notation "\spec_ B" (at level 0, format "\spec_ B"). *)
(* Reserved Notation "\spec" (at level 0, format "\spec"). *)
(* Reserved Notation "\refines_ r a b"  *)
(*          (at level 0, format "\refines_ r  a  b", *)
(*           r at level 0, a at next level). *)

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
Fact param_key : unit. Proof. done. Qed.
Fact getparam_key : unit. Proof. done. Qed.

Class param {A B} (R : A -> B -> Prop) (m : A) (n : B) := 
  param_rel : (locked_with param_key R) m n.
Arguments param {A B} R%rel_scope m n.

Class getparam {A B} (R : A -> B -> Prop) (m : A) (n : B) := 
  getparam_rel : (locked_with getparam_key R) m n.
Arguments getparam {A B} R%rel_scope m n.

Lemma paramE A B (R : A -> B -> Prop) : (param R = R) * (getparam R = R).
Proof. by rewrite /param /getparam !unlock. Qed.

Lemma param_eq T (x y : T) : param eq x y -> x = y.
Proof. by rewrite paramE. Qed.

Global Instance param_sub_proper {A B} :
   Proper (sub_hrel ==> eq ==> eq ==> impl) (@param A B).
Proof. by move=> R S RS x _ <- y _ <-; move: x y; rewrite !paramE. Qed.

Global Instance getparam_sub_proper {A B} :
   Proper (sub_hrel ==> eq ==> eq ==> impl) (@getparam A B).
Proof. by move=> R S RS x _ <- y _ <-; move: x y; rewrite !paramE. Qed.

Global Instance param_proper {A B} :
   Proper (eq_hrel ==> eq ==> eq ==> iff) (@param A B).
Proof. by move=> ?? [??] ??? ???; split; apply: param_sub_proper. Qed.

Global Instance getparam_proper {A B} :
   Proper (eq_hrel ==> eq ==> eq ==> iff) (@getparam A B).
Proof. by move=> ?? [??] ??? ???; split; apply: getparam_sub_proper. Qed.

Lemma getparam_eq A (a : A) : getparam eq a a.
Proof. by rewrite paramE. Qed.
Global Hint Extern 0 (getparam _ _ _)
  => now eapply @getparam_eq : typeclass_instances.

(* Lemma param_eq A (a : A) : param eq a a. *)
(* Proof. by rewrite paramE. Qed. *)

Global Instance param_apply 
   A B (R : A -> B -> Prop) C D (R' : C -> D -> Prop) :
   forall (c : A -> C) (d : B -> D), param (R ==> R') c d ->
   forall (a : A) (b : B), param R a b ->
(* --------------------------------------------------------- *)
   param R' (c a) (d b).
Proof. by rewrite !paramE => c d rcd a b rab; apply: rcd. Qed.

Lemma param_id (T T' : Type) (R : T -> T' -> Prop) :
   param (R ==> R) id id.
Proof. by rewrite !paramE. Qed.

Lemma id_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  param R x y -> param R x y.
Proof. done. Qed.

Lemma trivial_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  R x y -> param R x y.
Proof. by rewrite !paramE. Qed.
Global Hint Extern 0 (param _ _ _)
  => apply trivial_param; eassumption : typeclass_instances.

Lemma paramP T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  param R x y -> R x y.
Proof. by rewrite !paramE. Qed.

Lemma get_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
   getparam R x y -> param R x y.
Proof. by rewrite !paramE. Qed.

Lemma set_param T T' (R : T -> T' -> Prop) (x : T) (y : T') :
  param R x y -> getparam R x y.
Proof. by rewrite !paramE. Qed.
(* Global Hint Extern 999 (getparam refines _ _) *)
(*  => eapply set_param : typeclass_instances. *)

Fact composable_lock : unit. Proof. exact tt. Qed.

Class composable {A B C}
 (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) (rAC : A -> C -> Prop) := 
  Composable : locked_with composable_lock (rAB \o rBC <= rAC)%rel.
Arguments composable {A B C} rAB%rel rBC%rel rAC%rel.

Lemma composableE A B C
 (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) (rAC : A -> C -> Prop) :
  composable rAB rBC rAC = (rAB \o rBC <= rAC)%rel.
Proof. by rewrite /composable unlock. Qed.

Global Instance composable_sub_proper {A B C} :
   Proper (sub_hrel --> sub_hrel --> sub_hrel ==> impl) (@composable A B C).
Proof. 
move => R S RS T U TU V W VW; rewrite !composableE => RTV.
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
  composable rAB rBC rAC -> param rAB a b ->
  getparam rBC b c -> param rAC a c.
Proof.
by rewrite !paramE composableE => rABC rab rbc; apply: rABC; exists b.
Qed.

(* Local Instance refinement_trans A B C *)
(*   (rab : refinement A B) (rbc : refinement B C) : refinement A C :=  *)
(*   Refinement (@implem_composeK _ _ _ rab rbc). *)

(* Lemma refines_trans A B C (rab : refinement A B) (rbc : refinement B C) *)
(*   (a : A) (b : B) (c : C) `{!refines a b, !refines b c} : refines a c. *)
(* Proof. by do? rewrite /refines /= spec_refines. Qed. *)
(* (* rac := refinement_trans rab rbc and leaving it implicit in the *) *)
(* (* conclusion leads to a Bad implicit argument number: 11 *) *)

Lemma composable_rid1 A B (R : A -> B -> Prop): composable eq R R.
Proof. by rewrite composableE comp_eql. Qed.

Global Instance composable_comp A B C (rAB : A -> B -> Prop) (rBC : B -> C -> Prop) :
  composable rAB rBC (rAB \o rBC)%rel.
Proof. by rewrite composableE. Qed.

Lemma composable_imply {A B C A' B' C'}
  (rAB : A -> B -> Prop) (rBC : B -> C -> Prop)
  (R1 : A' -> B' -> Prop) (R2 : B' -> C' -> Prop) (R3 : A' -> C' -> Prop):
composable R1 R2 R3 -> composable (rAB ==> R1) (rBC ==> R2) (rAB \o rBC ==> R3).
Proof.
rewrite !composableE => R123.
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

Lemma RboolE (b b' : bool) : param Logic.eq b b' -> b = b'. 
Proof. by rewrite paramE. Qed.

(* Hint Extern 0 (refines _ _) => eapply paramR : typeclass_instances. *)

(* Hint Extern 0 (composable _ _ _) *)
(*  => now eapply composable_comp : typeclass_instances. *)

Typeclasses Opaque comp_hrel.

Hint Extern 0 (composable eq _ _)
 => now eapply composable_rid1 : typeclass_instances.

Hint Extern 0 (composable _ _ eq)
 => now eapply composable_rid1 : typeclass_instances.

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
(* Class refinement {A B} (R : A -> B -> Prop) := Refinement {}. *)

(* This class describes what is a term refinement *)
(* Definition refines {A B R} `{refinement A B R} := R. *)

Lemma getparam_abstr
   A   B   (R   : A   -> B   -> Prop)
   A'  B'  (R'  : A'  -> B'  -> Prop) 
   (f : A -> A' ) (g : B -> B') :
   (forall (a : A) (b : B), param R a b -> getparam R' (f a) (g b)) ->
(* ---------------------------------------------------------------------- *)
   getparam (R ==> R') f g.
Proof. by rewrite !paramE; apply. Qed.

Hint Extern 2 (getparam (_ ==> _) _ _)
 => eapply @getparam_abstr=>??? : typeclass_instances.

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

Global Hint Extern 1 (getparam _ _ _)
 => eapply set_param : typeclass_instances.

(* Global Hint Extern 1000 (getparam _ _ _) *)
(*  => eapply param_unfold : typeclass_instances. *)

Hint Extern 2 (getparam (_ ==> _) _ _)
 => eapply @getparam_abstr=> ??? : typeclass_instances.

(* Arguments refinement {A B} _%rel. *)

Section prod.
Context {A A' B B' : Type} (rA : A -> A' -> Prop) (rB : B -> B' -> Prop).

Definition prod_hrel : A * B -> A' * B' -> Prop :=
  fun x y => rA x.1 y.1 /\ rB x.2 y.2.

Lemma getparam_pair : 
  (getparam rA ==> getparam rB ==> getparam prod_hrel)%rel
    (@pair A B) (@pair A' B').
Proof. by rewrite !paramE. Qed.

Lemma getparam_fst :
  (getparam prod_hrel ==> getparam rA)%rel (@fst _ _) (@fst _ _).
Proof. by rewrite !paramE => [??] [??]. Qed.

Lemma getparam_snd :
  (getparam prod_hrel ==> getparam rB)%rel (@snd _ _) (@snd _ _).
Proof. by rewrite !paramE => [??] [??]. Qed.

Global Instance param_pair : 
  param (rA ==> rB ==> prod_hrel)%rel (@pair _ _) (@pair _ _).
Proof. by rewrite paramE. Qed.

Global Instance param_fst : param (prod_hrel ==> rA)%rel (@fst _ _) (@fst _ _).
Proof. by rewrite !paramE=> [??] [??]. Qed.

Global Instance param_snd : param (prod_hrel ==> rB)%rel (@snd _ _) (@snd _ _).
Proof. by rewrite !paramE=> [??] [??]. Qed.

End prod.
Arguments prod_hrel {_ _ _ _} rA%rel rB%rel _ _.
Notation "X * Y" := (prod_hrel X Y) : rel_scope.

Arguments getparam_pair {_ _ _ _ _ _ _ _ _ _ _ _}.
Arguments getparam_fst {_ _ _ _ _ _ _ _ _}.
Arguments getparam_snd {_ _ _ _ _ _ _ _ _}.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_pair : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_fst : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_snd : typeclass_instances.

Section sum.
Context {A A' B B' : Type} (rA : A -> A' -> Prop) (rB : B -> B' -> Prop).

Definition sum_hrel : A + B -> A' + B' -> Prop :=
  fun x y => match x, y with inl x, inl y => rA x y
                          | inr x, inr y => rB x y
                          | _, _ => False end.

Lemma getparam_inl :
  (getparam rA ==> getparam sum_hrel)%rel (@inl _ _) (@inl _ _).
Proof. by rewrite !paramE. Qed.

Lemma getparam_inr :
  (getparam rB ==> getparam sum_hrel)%rel (@inr _ _) (@inr _ _).
Proof. by rewrite !paramE. Qed.

Definition sum_elim {A B T} (ab : A + B) (f : A -> T) (g : B -> T) :=
  match ab with inl a => f a | inr b => g b end.

Lemma getparam_sum_rect T T' (R : T -> T' -> Prop) :
  (getparam sum_hrel ==> getparam (rA ==> R) ==>
            getparam (rB ==> R) ==> getparam R)%rel sum_elim sum_elim.
Proof.
rewrite !paramE => x x' rx f f' rf g g' rg.
by case: x x' rx=> [a|b] [a'|b'] //= rab; [apply: rf|apply: rg].
Qed.

Global Instance param_inl : param (rA ==> sum_hrel)%rel (@inl _ _) (@inl _ _).
Proof. by rewrite paramE. Qed.

Global Instance param_inr : param (rB ==> sum_hrel)%rel (@inr _ _) (@inr _ _).
Proof. by rewrite paramE. Qed.

End sum.
Arguments sum_hrel {_ _ _ _} rA%rel rB%rel _ _.
Notation "X + Y" := (sum_hrel X Y) : rel_scope.

Arguments getparam_inr {_ _ _ _ _ _ _ _ _}.
Arguments getparam_inl {_ _ _ _ _ _ _ _ _}.
Arguments getparam_sum_rect {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_sum_rect : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_inr : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_inl : typeclass_instances.

Section param_seq.
Context {A B : Type} (rAB : A -> B -> Prop).

Fixpoint seq_hrel sa sb : Prop :=
  match sa, sb with
    | [::],    [::]    => True
    | a :: sa, b :: sb => rAB a b /\ seq_hrel sa sb
    | _,       _       => False
  end.

Global Instance getparam_nil : getparam seq_hrel nil nil.
Proof. by rewrite paramE. Qed.

Lemma getparam_cons : 
  (getparam rAB ==> getparam seq_hrel ==> getparam seq_hrel)%rel cons cons.
Proof. by rewrite !paramE. Qed.

Lemma getparam_rcons : 
  (getparam seq_hrel ==> getparam rAB ==> getparam seq_hrel)%rel rcons rcons.
Proof.
have H: forall x x' s s', seq_hrel s s' -> rAB x x' -> seq_hrel (rcons s x) (rcons
s' x').
  move=> x x' s; elim: s => [|a s IHs] [] //= a' s' [r_aa' r_ss'] r_xx'.
  by split=> //; apply: IHs.
by rewrite !paramE => ??????; apply: H.
Qed.

Lemma getparam_foldr {C D : Type} (rCD : C -> D -> Prop) :
   (getparam (rAB ==> rCD ==> rCD) ==> getparam rCD ==> 
             getparam seq_hrel ==> getparam rCD)%rel foldr foldr.
Proof.
rewrite !paramE => f g rfg c d rcd; elim=> [|x s /= ihs] [|y t] //= [rxy rst].
by apply: rfg => //; apply: ihs.
Qed.

Lemma getparam_foldl {C D : Type} (rCD : C -> D -> Prop) :
   (getparam (rCD ==> rAB ==> rCD) ==> getparam rCD ==> 
             getparam seq_hrel ==> getparam rCD)%rel foldl foldl.
Proof.
rewrite !paramE => f g rfg c d rcd s.
elim: s c d rcd => [|x s /= ihs] c d rcd [|y t] //= [rxy rst].
by apply: ihs => //; apply: rfg.
Qed.

Lemma getparam_iter :
  (getparam Logic.eq ==> getparam (rAB ==> rAB) ==> getparam rAB ==>
  getparam rAB)%rel (@iter A) (@iter B).
Proof.
rewrite !paramE => n n' <- {n'}.
elim: n => [|n IHn] f f' rff' x x' rxx' //=.
by apply: (rff'); apply: IHn.
Qed.

Lemma getparam_size :
  (getparam seq_hrel ==> getparam eq)%rel size size.
Proof. by rewrite !paramE; elim=> [|x s IHs] [] // x' s' /= [_ /IHs ->]. Qed.

Lemma getparam_nth :
  (getparam rAB ==> getparam seq_hrel ==> getparam eq ==> getparam rAB)%rel nth nth.
Proof.
rewrite !paramE => x x' rxx'.
elim=> [|a s IHs] [|a' s'] //=; first by move=> ????; rewrite !nth_nil.
by case=> raa' rss' [|n] n' <- {n'} //=; apply: IHs.
Qed.

End param_seq.

Arguments getparam_cons {_ _ _ _ _ _ _ _ _}.
Arguments getparam_rcons {_ _ _ _ _ _ _ _ _}.
Arguments getparam_foldr {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments getparam_foldl {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments getparam_iter {_ _ _ _ _ _ _ _ _ _ _ _}.
Arguments getparam_size {_ _ _ _ _ _}.
Arguments getparam_nth {_ _ _ _ _ _ _ _ _ _ _ _}.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_cons : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_rcons : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_foldr : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_foldl : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_iter : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_size : typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_nth : typeclass_instances.

Lemma getparam_map A A' (rA : A -> A' -> Prop) B B' (rB : B -> B' -> Prop) : 
  (getparam (rA ==> rB) ==> getparam (seq_hrel rA) ==>
    getparam (seq_hrel rB))%rel map map.
Proof.
rewrite !paramE => f f' rf; elim => [|a sa iha] [|b sb] //= [rab rsab].
by split; [exact: rf|exact: iha].
Qed.
Arguments getparam_map {_ _ _ _ _ _ _ _ _ _ _ _}.
Hint Extern 1 (getparam _ _ _) =>
  eapply getparam_map : typeclass_instances.

Definition bool_if {A} (c : bool) (a b : A) : A := if c then a else b.

Lemma getparam_if {A A'} (R : A -> A' -> Prop) :
  (param eq ==> getparam R ==> getparam R ==> getparam R)%rel bool_if bool_if.
Proof. by rewrite paramE; move => [] _ <- ??? ???. Qed.

Hint Extern 1 (getparam _ _ _) => eapply getparam_if: typeclass_instances.

Section param_option.
Context {A B : Type} (rAB : A -> B -> Prop).

Fixpoint ohrel sa sb : Prop :=
  match sa, sb with
    | None,   None   => True
    | Some a, Some b => rAB a b
    | _,      _      => False
  end.

Global Instance getparam_None : getparam ohrel None None.
Proof. by rewrite paramE. Qed.

Lemma getparam_some : (rAB ==> ohrel)%rel some some.
Proof. by []. Qed.

End param_option.

Arguments getparam_some {_ _ _ _ _ _}.

Section param_nat.

Global Instance param_eq_zero : param Logic.eq 0%N 0%N.
Proof. by rewrite paramE. Qed.

Global Instance param_eq_succ : param (Logic.eq ==> Logic.eq) S S.
Proof. by apply param_abstr; rewrite paramE => ? ? ->. Qed.

End param_nat.
(*
This hint is too aggressively applied

Hint Extern 1 (getparam _ _ _) =>
  eapply param_Some : typeclass_instances.
*)

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
Class hzero {I} B := hzero_op : forall {m n : I}, B m n.
Local Notation "0" := hzero_op : hetero_computable_scope.

Class hone {I} B := hone_op : forall {n : I}, B n n.
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

Class hcast {I} B := castmx : forall m n m' n' : I,
  (m = m') * (n = n') -> B m n -> B m' n'.

(* Surgery on matrix-like data types *)
Local Open Scope nat_scope.
Class usub B := usubmx : forall (m1 m2 n : nat), B (m1 + m2) n -> B m1 n.
Class dsub B := dsubmx : forall (m1 m2 n : nat), B (m1 + m2) n -> B m2 n.
Class lsub B := lsubmx : forall (m n1 n2 : nat), B m (n1 + n2) -> B m n1.
Class rsub B := rsubmx : forall (m n1 n2 : nat), B m (n1 + n2) -> B m n2.
Class ulsub B := ulsubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n1.
Class ursub B := ursubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n2.
Class dlsub B := dlsubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n1.
Class drsub B := drsubmx : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n2.
Class row_mx_class B := row_mx : forall (m n1 n2 : nat),
  B m n1 -> B m n2 -> B m (n1 + n2).
Class col_mx_class B := col_mx : forall (m1 m2 n : nat),
  B m1 n -> B m2 n -> B (m1 + m2) n.
Class block B := block_mx : forall (m1 m2 n1 n2 : nat),
  B m1 n1 -> B m1 n2 -> B m2 n1 -> B m2 n2 -> B (m1 + m2) (n1 + n2).

Class const_mx_class A B :=
  const_mx : forall {m n : nat}, A -> B m n.

Class row_class I B := row : forall (m n : nat), I m -> B m n -> B 1 n.

Class col_class I B := col : forall (m n : nat), I n -> B m n -> B m 1.

Class row'_class I B := row' : forall (m n : nat), I m -> B m n -> B (predn m) n.

Class col'_class I B := col' : forall (m n : nat), I n -> B m n -> B m (predn n).

Class fun_of A I B :=
  fun_of_matrix : forall (m n : nat), B m n -> I m -> I n -> A.

Class scalar_mx_class A B := scalar_mx : forall {n : nat}, A -> B n n.

Class tperm_class A S :=
  tperm : A -> A -> S.

Class lift0_perm_class S :=
  lift0_perm : forall (n : nat), S n -> S n.+1.

Class xrow_class I B :=
  xrow : forall (m n : nat), I m -> I m -> B m n -> B m n.

Class xcol_class I B :=
  xcol : forall (m n : nat), I n -> I n -> B m n -> B m n.

Class row_perm_class S B :=
  row_perm : forall (m n : nat), S m -> B m n -> B m n.

Class col_perm_class S B :=
  col_perm : forall (m n : nat), S n -> B m n -> B m n.

Class spec_of (A B : Type) := spec : A -> B.
(* Class implem_of A B := implem : A -> B. *)
Definition spec_id {A : Type} : spec_of A A := id.

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
Notation "*:%C"   := scale_op.
Notation "x *: y" := (scale_op x y) : computable_scope.
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
Notation "+%HC"    := hadd_op.
Notation "x + y"  := (hadd_op x y)   : hetero_computable_scope.
Notation "x - y"  := (hsub_op x y)   : hetero_computable_scope.
Notation "x == y" := (heq_op x y)    : hetero_computable_scope.
Notation "a %:M"  := (scalar_mx a)   : hetero_computable_scope.
Notation "*m%C"   := hmul_op.
Notation "x *m y" := (hmul_op x y)   : hetero_computable_scope.
Notation "x '.(' i ',' j ')'" := (fun_of_matrix x i j) (at level 10) : computable_scope.

(* TODO: fold patterns for unapplied op *)

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
      | rewrite -[heq_op _ _]/(_ == _)%bool
      | rewrite -[hmul_op _ _]/(mulmx _ _)
      | rewrite -[castmx _ _]/(matrix.castmx _ _)
      | rewrite -[usubmx _]/(matrix.usubmx _)
      | rewrite -[dsubmx _]/(matrix.dsubmx _)
      | rewrite -[lsubmx _]/(matrix.lsubmx _)
      | rewrite -[rsubmx _]/(matrix.rsubmx _)
      | rewrite -[ulsubmx _]/(matrix.ulsubmx _)
      | rewrite -[ursubmx _]/(matrix.ursubmx _)
      | rewrite -[dlsubmx _]/(matrix.dlsubmx _)
      | rewrite -[drsubmx _]/(matrix.drsubmx _)
      | rewrite -[row_mx _ _]/(matrix.row_mx _ _)
      | rewrite -[col_mx _ _]/(matrix.col_mx _ _)
      | rewrite -[block_mx _ _ _ _]/(matrix.block_mx _ _ _ _)
      | rewrite -[fun_of_matrix _]/(matrix.fun_of_matrix _)
      | rewrite -[const_mx _]/(matrix.const_mx _)
      | rewrite -[scalar_mx _]/(matrix.scalar_mx _)
      | rewrite -[tperm _ _]/(perm.tperm _ _)
      | rewrite -[lift0_perm _]/(matrix.lift0_perm _)
      | rewrite -[row_perm _ _]/(matrix.row_perm _ _)
      | rewrite -[xrow _ _ _]/(matrix.xrow _ _ _)].

(* Opacity of ssr symbols *)
Typeclasses Opaque eqtype.eq_op.
Typeclasses Opaque addn subn muln expn.
Typeclasses Opaque GRing.zero GRing.add GRing.opp GRing.natmul.
Typeclasses Opaque GRing.one GRing.mul GRing.inv GRing.exp GRing.scale.
Typeclasses Opaque Num.le Num.lt Num.norm.
Typeclasses Opaque intmul exprz absz.
Typeclasses Opaque matrix.usubmx matrix.dsubmx matrix.lsubmx matrix.rsubmx.
Typeclasses Opaque matrix.ulsubmx matrix.ursubmx matrix.dlsubmx matrix.drsubmx.
Typeclasses Opaque matrix.row_mx matrix.col_mx matrix.block_mx matrix.castmx.

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

Lemma specE A C (R : A -> C -> Prop) `{spec_of C A} :
  (param (R ==> Logic.eq) spec_id spec) ->
  forall a c, param R a c -> spec c = a.
Proof.
move=> pf a c rac; rewrite -[a]/(idfun a).
by symmetry; apply: paramP.
Qed.
