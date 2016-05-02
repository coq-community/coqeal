Require Import ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

From CoqEAL Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

Local Open Scope ring_scope.

Section binord_op.

Definition binord := fun (_ : nat) => N.

Global Instance implem_ord n : implem_of 'I_n (binord n) := bin_of_nat.

End binord_op.

Section binord_theory.

Local Open Scope rel_scope.

Definition Rord n1 n2 (rn : nat_R n1 n2) : 'I_n1 -> binord n2 -> Type :=
  fun x m => bin_of_nat x = m.

Lemma ordinal_R_eq n1 n2 (rn : nat_R n1 n2) x y :
  ordinal_R rn x y -> x = y :> nat.
Proof.
  case=> m1 m2 rm hi hj _ /=.
  by rewrite (nat_R_eq rm).
Qed.

Global Instance Rord_implem n1 n2 (rn : nat_R n1 n2) :
  refines (ordinal_R rn ==> Rord rn) implem_id implem.
Proof.
  rewrite refinesE=> x y rxy.
  rewrite /Rord /implem_id /implem /implem_ord.
  by rewrite (@ordinal_R_eq n1 n2 rn x y rxy).
Qed.

Variable (N : Type) (Rnat : nat -> N -> Type).
Context `{implem_of nat N}.
Context `{!refines (Logic.eq ==> Rnat) implem_id implem}.

Local Open Scope fun_scope.

Global Instance Rnat_nat_of_ord n1 n2 (rn : nat_R n1 n2) :
  refines (Rord rn ==> Rnat) (@nat_of_ord n1) (implem \o nat_of_bin).
Proof.
  rewrite refinesE /funcomp=> x y hxy.
  rewrite -hxy bin_of_natK -{1}[_ x]/(implem_id _).
  have hx : refines eq (nat_of_ord x) (nat_of_ord x) by rewrite refinesE.
  exact: refinesP.
Qed.

End binord_theory.