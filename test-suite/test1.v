Require Import List.

(*
Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "abstraction". *)

Require Import test_eq.

(** Inductive **)
Translate Inductive nat.
Translate Inductive list.
Translate Inductive bool.
Translate Inductive option.

Translate Inductive option Arity 1.
Translate Inductive list Arity 1.
Translate Inductive nat Arity 1.
Translate Inductive nat Arity 10.

Translate Inductive False.
Translate Inductive or.

Translate In.
Next Obligation.
destruct l; reflexivity.
Defined.

Definition eq_R_transport :
 forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (x₁ : A₁) (x₂ : A₂),
         A_R x₁ x₂ -> forall (H : A₁) (H0 : A₂), A_R H H0 -> x₁ = H -> x₂ = H0 -> Prop.
 intros A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R p q.
 pose (x_R' := transport (A_R x₁) q x_R).
 pose (x_R'' := transport (fun y => A_R y _) p x_R').
 exact (x_R'' = y_R).
Defined.

Lemma eq_R_transport_equiv :  
  forall A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R p q, eq_R_transport A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R p q -> eq_R A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R p q.
intros.
destruct p.
destruct q.
compute in *.
rewrite H.
constructor.
Defined.

Lemma eq_R_transport_equiv_inv :  
  forall A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R p q, eq_R A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R p q -> eq_R_transport A₁ A₂ A_R x₁ x₂ x_R y₁ y₂ y_R p q.
intros.
destruct H.
reflexivity.
Defined.

(** Match with *)
Translate pred.
Translate hd.
Translate pred Arity 10.

(** Fixpoint **)
Translate plus.
Next Obligation. destruct n; reflexivity. Defined.
Translate mult.
Next Obligation. destruct n; reflexivity. Defined.
Translate plus Arity 1.
Next Obligation. destruct n; reflexivity. Defined.
Translate mult Arity 1.
Next Obligation. destruct n; reflexivity. Defined.
Translate plus Arity 10.
Next Obligation. destruct n; reflexivity. Defined.
Translate mult as mult_R_test Arity 10.
Next Obligation. destruct n; reflexivity. Defined.

(** Section **)

Section Group.

Variable A : Type.
Variable e : A.
Variable dot : A -> A -> A.
Variable inv : A -> A.

Infix "×" := (dot) (at level 60).

Variable neutral : forall x, x × e = x.
Variable assoc : forall x y z, x×(y×z) = (x×y)×z.
Variable inverse: forall x, x × (inv x) = e.

Record fingrp (l : list A) := {
  fingrp_neutral : In e l; 
  fingrp_dot : forall x y, In x l -> In y l -> In (x×y) l;
  fingrp_inv : forall x, In x l -> In (inv x) l}.

Definition Fingrp := { l : list A & fingrp l }.

Definition operator := Fingrp -> Fingrp.


Variable f : A -> A.

Variable morphism_dot : 
  forall x y, f (x × y) = (f x) × (f y).
Variable morphism_neutral : f e = e.
Variable morphism_inv : forall x, f (inv x) = inv (f x).

Realizer A As graph := (fun (x y : A) => f x = y).
Realizer e As e_R := morphism_neutral.
Realizer dot As dot_R := _.
Next Obligation.
unfold graph.
rewrite morphism_dot.
rewrite X1.
rewrite X4.
reflexivity.
Defined.
Realizer inv As inv_R := _.
Next Obligation.
compute.
rewrite morphism_inv.
rewrite X1; reflexivity.
Defined.


Variable A_set : hSet A. 

Realizer neutral As A_neutral_R := _.
Next Obligation.
apply eq_R_transport_equiv.
apply A_set.
Defined.

Realizer assoc As A_assoc_R := _.
Next Obligation.
apply eq_R_transport_equiv.
apply A_set.
Defined.

Realizer inverse As A_inverse_R := _.
Next Obligation.
apply eq_R_transport_equiv.
apply A_set.
Defined.

Realizer A_set As A_set_R := _.
Next Obligation.
pose (H := hSet_auto _ A_set graph).
unfold hSet_R in H.
apply eq_R_transport_equiv.
assert (eq_refl = q₁).
apply A_set.
assert (eq_refl = q₂).
apply A_set.
assert (x_R = y_R).
apply A_set.
destruct H.
destruct H0.
destruct H1.
pose (eq_R_transport_equiv_inv _ _ _ _ _ _ _ _ _ _ _ p_R).
pose (eq_R_transport_equiv_inv _ _ _ _ _ _ _ _ _ _ _ q_R).
unfold eq_R_transport in e0, e1.
simpl in e0, e1.


Check x_R.
unfold eq_R_transport.
Check eq_R.

unfold eq_R in p_R.
unfold eq_R in p_R. q_R.
unfold graph in *.

unfold eq_R_transport.
