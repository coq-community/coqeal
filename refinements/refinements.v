From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
(* Require Import path choice fintype tuple finset ssralg bigop poly polydiv. *)
(* Require Import ssrint ZArith. *)

From CoqEAL Require Import hrel param.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic. *)

Delimit Scope computable_scope with C.
Local Open Scope rel.

(* Shortcut for triggering typeclass resolution *)
Ltac tc := do 1?typeclasses eauto.

Section refinements.

Fact refines_key : unit. Proof. done. Qed.
Class refines A B (R : A -> B -> Type) (m : A) (n : B) :=
  refines_rel : (locked_with refines_key R) m n.
Arguments refines A B R%rel m n.

Lemma refinesE A B (R : A -> B -> Type) : refines R = R.
Proof. by rewrite /refines unlock. Qed.

Lemma refines_eq T (x y : T) : refines eq x y -> x = y.
Proof. by rewrite refinesE. Qed.

Global Instance refines_bool_eq x y : refines bool_R x y -> refines eq x y.
Proof. by rewrite !refinesE=> [[]]. Qed.

Lemma nat_R_eq x y : nat_R x y -> x = y.
Proof. by elim=> // m n _ ->. Qed.

Global Instance refines_nat_eq x y : refines nat_R x y -> refines eq x y.
Proof. rewrite !refinesE; exact: nat_R_eq. Qed.

Lemma refinesP T T' (R : T -> T' -> Type) (x : T) (y : T') :
  refines R x y -> R x y.
Proof. by rewrite refinesE. Qed.

Fact composable_lock : unit. Proof. done. Qed.
Class composable A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :=
  Composable : locked_with composable_lock (rAB \o rBC <= rAC).

Lemma composableE A B C
 (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :
  composable rAB rBC rAC = (rAB \o rBC <= rAC).
Proof. by rewrite /composable unlock. Qed.

Lemma refines_trans A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type)
  (a : A) (b : B) (c : C) : composable rAB rBC rAC ->
  refines rAB a b -> refines rBC b c -> refines rAC a c.
Proof.
by rewrite !refinesE composableE => rABC rab rbc; apply: rABC; exists b.
Qed.

Lemma trivial_refines T T' (R : T -> T' -> Type) (x : T) (y : T') :
  R x y -> refines R x y.
Proof. by rewrite refinesE. Qed.

Global Instance refines_apply
  A B (R : A -> B -> Type) C D (R' : C -> D -> Type) :
  forall (c : A -> C) (d : B -> D), refines (R ==> R') c d ->
  forall (a : A) (b : B), refines R a b -> refines R' (c a) (d b) | 99.
Proof. by rewrite !refinesE => c d rcd a b rab; apply: rcd. Qed.

Global Instance composable_rid1 A B (R : A -> B -> Type) :
  composable eq R R | 1.
Proof.
rewrite composableE; apply: eq_hrelRL.
by split; [ apply: comp_eql | move=> x y hxy; exists x ].
Qed.

Global Instance composable_bool_id1 B (R : bool -> B -> Type) :
  composable bool_R R R | 1.
Proof. by rewrite composableE => x y [y' [[]]]. Qed.

(* Global Instance composable_nat_id1 B (R : nat -> B -> Type) :
  composable nat_R R R | 1. *)
(* Proof. by rewrite composableE => x y [y' [/nat_R_eq ->]]. Qed. *)

Global Instance composable_comp A B C (rAB : A -> B -> Type)
  (rBC : B -> C -> Type) : composable rAB rBC (rAB \o rBC).
Proof. by rewrite composableE. Qed.

Global Instance composable_imply A B C A' B' C'
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (R1 : A' -> B' -> Type)
  (R2 : B' -> C' -> Type) (R3 : A' -> C' -> Type) : composable R1 R2 R3 ->
  composable (rAB ==> R1) (rBC ==> R2) (rAB \o rBC ==> R3) | 0.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c [b [rABab rBCbc]].
apply: R123; exists (fB b); split; [ exact: RfAB | exact: RfBC ].
Qed.

Global Instance composable_imply_id1 A B A' B' C'
  (rAB : A -> B -> Type) (R1 : A' -> B' -> Type) (R2 : B' -> C' -> Type)
  (R3 : A' -> C' -> Type) : composable R1 R2 R3 ->
  composable (eq ==> R1) (rAB ==> R2) (rAB ==> R3) | 1.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c rABac.
apply: R123; exists (fB a); split; [ exact: RfAB | exact: RfBC ].
Qed.

(* Composable and pairs *)
Lemma prod_hrel_R A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_R rA rB x y -> prod_hrel rA rB x y.
Proof. by case; split. Qed.

Global Instance composable_prod A A' B B' C C'
  (rAB : A -> B -> Type) (rAB' : A' -> B' -> Type)
  (rBC : B -> C -> Type) (rBC' : B' -> C' -> Type)
  (rAC : A -> C -> Type) (rAC' : A' -> C' -> Type) :
    composable rAB rBC rAC ->
    composable rAB' rBC' rAC' ->
    composable (prod_hrel rAB rAB') (prod_R rBC rBC')
               (prod_R rAC rAC') | 1.
Proof.
rewrite !composableE=> h1 h2 [a a'] [c c'] [[b b']].
case=> [[/= rab rab']] /prod_hrel_R [/= rbc rbc'].
by split; [ apply: h1; exists b | apply: h2; exists b'].
Qed.

Section refines_split.
Context {T} {Y} {Z} {R1 : T -> Y -> Type} {R2 : Y -> Z -> Type} {x : T} {z : Z}.

Lemma refines_split :
  refines (R1 \o R2) x z -> {y : Y & (refines R1 x y * refines R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split1 :
  refines (R1 \o R2) x z -> {y : Y & (refines R1 x y * R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split2 :
  refines (R1 \o R2) x z -> {y : Y & (R1 x y * refines R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split12 :
  refines (R1 \o R2) x z -> {y : Y & (R1 x y * R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

End refines_split.

Lemma refines_abstr A B C D (R : A -> B -> Type) (R' : C -> D -> Type)
      (c : A -> C) (d : B -> D):
        (forall (a :  A) (b : B), refines R a b -> refines R' (c a) (d b)) ->
        refines (R ==> R') c d.
Proof. by rewrite !refinesE; apply. Qed.

Lemma refines_abstr2 A B A' B' A'' B''
      (R : A -> B -> Type) (R' : A' -> B' -> Type) (R'' : A'' -> B'' -> Type)
      (f : A -> A' -> A'' ) (g : B -> B' -> B''):
        (forall (a : A)   (b : B), refines R a b ->
         forall (a' : A') (b' : B'), refines R' a' b' ->
        refines R'' (f a a') (g b b')) ->
        refines (R ==> R' ==> R'') f g.
Proof. by move=> H; do 2![eapply refines_abstr => *]; apply: H. Qed.

Global Instance refines_pair
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (rA ==> rB ==> prod_hrel rA rB)%rel (@pair _ _) (@pair _ _).
Proof. by rewrite refinesE. Qed.

Global Instance refines_fst
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_hrel rA rB ==> rA)%rel (@fst _ _) (@fst _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Global Instance refines_snd
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_hrel rA rB ==> rB)%rel (@snd _ _) (@snd _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Global Instance refines_pair_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (rA ==> rB ==> prod_R rA rB)%rel (@pair _ _) (@pair _ _).
Proof. by rewrite refinesE. Qed.

Global Instance refines_fst_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_R rA rB ==> rA)%rel (@fst _ _) (@fst _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Global Instance refines_snd_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_R rA rB ==> rB)%rel (@snd _ _) (@snd _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Class unify A (x y : A) := unify_rel : x = y.
Global Instance unifyxx A (x : A) : unify x x := erefl.

Global Instance refines_of_unify A x y : unify x y -> refines (@unify A) x y | 100.
Proof. by rewrite refinesE. Qed.

Lemma refines_comp_unify A B (R : A -> B -> Type) x y :
  refines (R \o (@unify B))%rel x y -> refines R x y.
Proof.
  rewrite !refinesE=> H.
  case: H=> ? h.
  case: h=> ? h2.
  by rewrite -h2.
Qed.

End refinements.

Hint Mode refines - - - + - : typeclass_instances.

Hint Extern 0 (refines _ _ _)
  => apply trivial_refines; eassumption : typeclass_instances.

Hint Extern 0 (refines (_ \o (@unify _))%rel _ _)
  => eapply refines_trans : typeclass_instances.

(* Tactic for doing parametricity proofs, it takes a parametricity
   theorem generated by the Parametricity plugin as argument *)
Ltac param x :=
  rewrite ?refinesE; do?move=> ?*;
  eapply x=> *; eapply refinesP;
  do ?eapply refines_apply; tc.

(* Special tactic when relation is defined using \o *)
Ltac param_comp x := eapply refines_trans; tc; param x.

Global Instance refines_true : refines _ _ _ :=
  trivial_refines bool_R_true_R.

Global Instance refines_false : refines _ _ _ :=
  trivial_refines bool_R_false_R.

Global Instance refines_negb : refines (bool_R ==> bool_R) negb negb.
Proof. exact/trivial_refines/negb_R. Qed.

Global Instance refines_implb : refines (bool_R ==> bool_R ==> bool_R) implb implb.
Proof. exact/trivial_refines/implb_R. Qed.

Global Instance refines_andb : refines (bool_R ==> bool_R ==> bool_R) andb andb.
Proof. exact/trivial_refines/andb_R. Qed.

Global Instance refines_orb : refines (bool_R ==> bool_R ==> bool_R) orb orb.
Proof. exact/trivial_refines/orb_R. Qed.

Global Instance refines_addb : refines (bool_R ==> bool_R ==> bool_R) addb addb.
Proof. exact/trivial_refines/addb_R. Qed.

Global Instance refines_eqb : refines (bool_R ==> bool_R ==> bool_R) eqtype.eq_op eqtype.eq_op.
Proof. exact/trivial_refines/eqb_R. Qed.

Lemma refines_goal (G G' : Type) : refines (fun T T' => T' -> T) G G' -> G' -> G.
Proof. by rewrite refinesE. Qed.

Global Instance refines_leibniz_eq (T : eqType) (x y : T) b :
  refines bool_R (x == y) b -> refines (fun T' T => T -> T') (x = y) b.
Proof. by move=> /refines_bool_eq; rewrite !refinesE => <- /eqP. Qed.

Ltac CoqEAL := apply: refines_goal; vm_compute.

Module Refinements.

(* Generic operations *)
Module Op.

Class zero_of A := zero_op : A.
Hint Mode zero_of + : typeclass_instances.
Class one_of A := one_op : A.
Hint Mode one_of + : typeclass_instances.
Class opp_of A := opp_op : A -> A.
Hint Mode opp_of + : typeclass_instances.
Class add_of A := add_op : A -> A -> A.
Hint Mode add_of + : typeclass_instances.
Class sub_of A := sub_op : A -> A -> A.
Hint Mode sub_of + : typeclass_instances.
Class mul_of A := mul_op : A -> A -> A.
Hint Mode mul_of + : typeclass_instances.
Class exp_of A B := exp_op : A -> B -> A.
Hint Mode exp_of + + : typeclass_instances.
Class div_of A := div_op : A -> A -> A.
Hint Mode div_of + : typeclass_instances.
Class inv_of A := inv_op : A -> A.
Hint Mode inv_of + : typeclass_instances.
Class mod_of A := mod_op : A -> A -> A.
Hint Mode mod_of + : typeclass_instances.
Class scale_of A B := scale_op : A -> B -> B.
Hint Mode scale_of + + : typeclass_instances.

Class eq_of A := eq_op : A -> A -> bool.
Hint Mode eq_of + : typeclass_instances.
Class leq_of A := leq_op : A -> A -> bool.
Hint Mode leq_of + : typeclass_instances.
Class lt_of A := lt_op : A -> A -> bool.
Hint Mode lt_of + : typeclass_instances.
Class size_of A N := size_op : A -> N.
Hint Mode size_of + + : typeclass_instances.

Class spec_of A B   := spec : A -> B.
Hint Mode spec_of + + : typeclass_instances.
Definition spec_id {A : Type} : spec_of A A := id.
Class implem_of A B := implem : A -> B.
Hint Mode implem_of + + : typeclass_instances.
Definition implem_id {A : Type} : implem_of A A := id.
Class cast_of A B  := cast_op : A -> B.
Hint Mode cast_of + + : typeclass_instances.

End Op.
End Refinements.

Import Refinements.Op.

Typeclasses Transparent zero_of one_of opp_of add_of sub_of mul_of exp_of div_of
            inv_of mod_of scale_of size_of eq_of leq_of lt_of spec_of implem_of cast_of.

Arguments spec / : assert.

Notation "0"      := zero_op        : computable_scope.
Notation "1"      := one_op         : computable_scope.
Notation "-%C"    := opp_op.
Notation "- x"    := (opp_op x)     : computable_scope.
Notation "+%C"    := add_op.
Notation "x + y"  := (add_op x y)   : computable_scope.
Notation "x - y"  := (sub_op x y)   : computable_scope.
Notation "*%C"    := mul_op.
Notation "x * y"  := (mul_op x y)   : computable_scope.
Notation "x ^ y"  := (exp_op x y)   : computable_scope.
Notation "x %/ y" := (div_op x y)   : computable_scope.
Notation "x ^-1"  := (inv_op x)     : computable_scope.
Notation "x %% y" := (mod_op x y)   : computable_scope.
Notation "*:%C"   := scale_op.
Notation "x *: y" := (scale_op x y) : computable_scope.
Notation "x == y" := (eq_op x y)    : computable_scope.
Notation "x <= y" := (leq_op x y)   : computable_scope.
Notation "x < y"  := (lt_op x y)    : computable_scope.
Notation cast     := (@cast_op _).

Ltac simpC :=
  do ?[ rewrite -[0%C]/0%R
      | rewrite -[1%C]/1%R
      | rewrite -[(_ + _)%C]/(_ + _)%R
      | rewrite -[(_ + _)%C]/(_ + _)%N
      | rewrite -[(- _)%C]/(- _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%N
      | rewrite -[(_ * _)%C]/(_ * _)%R
      | rewrite -[(_ * _)%C]/(_ * _)%N
      | rewrite -[(_ %/ _)%C]/(_ %/ _)%R
      | rewrite -[(_ %% _)%C]/(_ %% _)%R
      | rewrite -[(_ == _)%C]/(_ == _)%bool
      ].

(* Section testmx. *)
(* Variable mxA : nat -> nat -> Type. *)
(* Definition idmx (m n : nat) (mx : mxA m n) : mxA m n := mx. *)
(* End testmx. *)
(* Parametricity idmx. *)
(* Print idmx_R. (* Here we get something too general! *) *)

Class reduce_in_spec {T} (x y : T) := Reduce : x = y.
Hint Mode reduce_in_spec - + - : typeclass_instances.

Hint Extern 0 (reduce_in_spec (spec _) _) =>
let x := fresh "x" in set x := (X in spec X);
vm_compute in (value of x); simpl; reflexivity : typeclass_instances.

Lemma refine_value_of {T} (x : T) {y y' : T}
      {rxy : refines eq (spec_id x) y} {rr : reduce_in_spec y y'} : x = y'.
Proof. by rewrite -rr; apply: refines_eq. Qed.

Notation refine_value x := (@refine_value_of _ x _ _ _ _).

Notation refine_value_for x x' := (@refine_value_of _ x' _ _ _ _ : x = _).
