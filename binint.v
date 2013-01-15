(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop ssrint.
Require Import ZArith.
Require Import refinements.
Require Import generic_quotient.

(******************************************************************************)
(* The binary integers of Coq is a refinement of SSReflects integers (ssrint) *) 
(*                                                                            *)
(* ??? == some documentation                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope signature_scope.

Import GRing.Theory.

Section binint.

Definition implem_int m := match m with
  | Posz m' => Z_of_nat m'
  | Negz m' => (- Z_of_nat(m'.+1))%Z
  end.

Lemma implem_int_inj : injective implem_int.
Proof.
case=> m; case=> /= n.
+ by move/Nat2Z.inj => ->.
+ move=> eq_mn.
  have := (Nat2Z.is_nonneg m).
  by rewrite eq_mn; case/Zle_not_lt; apply: Zlt_neg_0.
+ move=> eq_mn.
  have := (Nat2Z.is_nonneg n).
  by rewrite -eq_mn; case/Zle_not_lt; apply: Zlt_neg_0.
+ by move/Pos2Z.inj_neg/SuccNat2Pos.inj => ->.
Admitted.

Global Instance has_implemZ : has_implem int Z := @HasImplem _ _ implem_int implem_int_inj.
Global Instance Z_refinement_of_int : refinement_of int int Z := Refinement.

Global Program Instance ZeroZ : Zero Z := 0%Z.
Global Program Instance refines_int_0 : refines 0%R 0%Z := Refines 0 _ _.

Lemma id_refines_implem (A C : Type) {iAC : has_implem A C} (rAAC : refinement_of A A C)
  (a : A) (c : C) (ra : refines a c) : implem a = c.
Proof. by rewrite -[c]refines_implem -[a in LHS]refines_pi. Qed.

Global Program Instance CompZ : Comp Z := Z.eqb.
Global Program Instance refines_int_comp (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x == y) (x' == y')%C := Refines (x == y) _ _.
Next Obligation.
rewrite /comp /CompZ; case: (Z.eqb_spec _ _) => h.
  by apply/eqP; apply: implem_inj; rewrite !id_refines_implem.
apply/negP => /eqP eq_xy; apply: h.
by rewrite -[LHS]id_refines_implem eq_xy id_refines_implem.
Qed.

Global Program Instance AddZ : Add Z := fun x y => (x + y)%Z.
Global Program Instance AddMorphZ (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x + y) (x' + y')%C :=
  Refines (x + y) _ _.
Next Obligation.
rewrite /add /AddZ -[x']id_refines_implem -[y']id_refines_implem /=.
elim: x rx; first by rewrite add0r.
Admitted.

Global Program Instance OneZ : One Z := 1%Z.
Global Program Instance refines_int_1 : refines 1%R 1%Z := Refines 1 _ _.

Global Program Instance MulZ : Mul Z := fun x y => (x * y)%Z.
Global Program Instance MulMorphZ (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x * y) (x' * y')%C := Refines (x * y) _ _.
Next Obligation.
rewrite /mul /MulZ -[x']id_refines_implem -[y']id_refines_implem /=.
elim: x rx; first by rewrite mul0r.
Admitted.

End binint.

(* (* Some tests *) *)
(* Eval compute in 0%C. *)
(* Eval compute in (1 + 1 * 1 + 1)%C. *)