(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop ssrint.
Require Import ZArith.
Require Import refinements.

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
Qed.

Global Program Instance ImplemZ : Implem int Z := implem_int.
Global Program Instance Refines_int_Z : Refines ImplemZ.
Obligation 1. exact: implem_int_inj. Qed.

Global Program Instance ZeroZ : Zero Z := 0%Z.
Global Program Instance ZeroMorphZ : Morph implem 0 0%Z.
Obligation 1. by []. Qed.

Global Program Instance CompZ : Comp Z := fun x y => Z.eqb x y.
Global Program Instance CompMorphZ : 
  Morph (implem ==> implem ==> implem) (fun x y => x == y) (fun x y => x == y)%C.
Obligation 1.
rewrite /implem {3}/implem_op /ImplemId /= => x _ <- y _ <- /=.
rewrite /Comp /comp /CompZ.
case: (Z.eqb_spec (| x |) (| y |))%C => h.
  by rewrite -(inj_implem h) eqxx. 
apply/negP => /eqP heq.
by move: h; rewrite heq.
Qed.

Global Program Instance AddZ : Add Z := fun x y => (x + y)%Z.
Global Program Instance AddMorphZ :
  Morph (implem ==> implem ==> implem) (fun x y => x + y) (fun x y => x + y)%C.
Obligation 1.
rewrite /implem => x _ <- y _ <-.
elim: x; first by rewrite add0r.
  admit.
admit.
Defined.

Global Program Instance OneZ : One Z := 1%Z.
Global Program Instance OneMorphZ : Morph implem 1 1%C.
Obligation 1. by []. Qed.

Global Program Instance MulZ : Mul Z := fun x y => (x * y)%Z.
Global Program Instance MulMorphZ : Morph (implem ==> implem ==> implem) *%R mul.
Obligation 1.
rewrite /implem => x _ <- y _ <-.
elim: x; first by rewrite mul0r.
  admit.
admit.
Qed.

End binint.

(* (* Some tests *) *)
(* Eval compute in 0%C. *)
(* Eval compute in (1 + 1 * 1 + 1)%C. *)