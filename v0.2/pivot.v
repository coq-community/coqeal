(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset fingroup perm ssralg.
Require Import bigop matrix mxalgebra.

Require Import refinements hrel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section generic.

Variable A : Type.

Import Refinements.Op.

Variable mxA : nat -> nat -> Type.
Variable ordA : nat -> Type.
Variable permA : nat -> Type.

Context `{forall m, zero (ordA (1 + m))}.
Context `{zero A}.
Context `{forall m, zero (ordA m.+1)}.
Context `{fun_of A ordA mxA}.
Context `{lift0_class ordA}.
Context `{dsub mxA}.

Fixpoint find_pivot m n (P : A -> bool) {struct m} :
  mxA m n.+1 -> option (ordA m) :=
  if m is m'.+1 return mxA m n.+1 -> option (ordA m) then
     fun (M : mxA (1 + m') (1 + n)) =>
     if P (fun_of_matrix M 0 0)%C then
       obind (fun r => Some (lift0 r)) (find_pivot P (dsubmx M))
     else Some 0%C : option (ordA m'.+1)
  else fun (M : mxA O n.+1) => None : option (ordA O).

End generic.

Arguments find_pivot {A _ _ _ _ _ _ _} [m n] P M.

(*
Section seqmx.

Import Refinements.

Variable A : Type.

Context `{Op.zero A}.

Instance find_pivot_seqmx :
  Refinements.Op.find_pivot_class A (fun _ => nat)
    (fun _ _ => seqmatrix A) :=
  @find_pivot _ _ _ _ _ _ _ _.

End seqmx.
*)

Section correctness.

Import Refinements.

Variable A : Type.

Instance : Op.fun_of A ordinal (matrix A) := (@fun_of_matrix A).
Instance : Op.dsub (matrix A) := @matrix.dsubmx A.

Instance : forall m, Op.zero (ordinal (1 + m)) := fun _ => 0%R.
Instance : forall m, Op.zero (ordinal m.+1) := fun _ => 0%R.
Instance : Op.lift0_class ordinal := fun m i => lift 0%R i.

Lemma find_pivotP m n (M : 'M[A]_(m,n.+1)) P :
  pick_spec [pred i | P (M i 0%R)] (find_pivot P M).
Proof.
admit.
Qed.

End correctness.

(*
Section parametricity.

Import Refinements.

Context (A : Type) (C : Type) (rAC : A -> C -> Prop).
Definition RseqmxA {m n} := (@Rseqmx A m n \o (seq_hrel (seq_hrel rAC)))%rel.

Instance : Op.fun_of A ordinal (matrix A) := (@fun_of_matrix A).
Instance : Op.dsub (matrix A) := @matrix.dsubmx A.

Instance : forall m, Op.zero (ordinal (1 + m)) := fun _ => 0%R.
Instance : forall m, Op.zero (ordinal m.+1) := fun _ => 0%R.
Instance : Op.lift0_class ordinal := fun m i => lift 0%R i.

Context `{Op.zero C}.

(*
Context `{forall m, zero (ordA (1 + m))}.
Context `{forall m, zero (ordA m.+1)}.
Context `{fun_of A ordA mxA}.
Context `{lift0_class ordA}.
Context `{dsub mxA}.
*)

Notation ord := (fun _ : nat => nat).
Notation hseqmatrix := (fun (_ _ : nat) => seqmatrix C).

Context `{forall m1 m2 n, param (RseqmxA ==> RseqmxA)
  (@matrix.dsubmx A m1 m2 n)  (@Op.dsubmx _ _ m1 m2 n)}.

Global Instance RseqmxA_find_pivot m n :
  param ((rAC ==> Logic.eq) ==> RseqmxA ==> ohrel (@Rord m)) (@find_pivot A _ _ _ _ _ _ _ m n) (@find_pivot C hseqmatrix ord _ _ _ _ _ m n).
Proof.
elim: m => [|m IHm]; first exact: get_param.
rewrite /=.
eapply get_param.
eapply getparam_abstr => ? ? ?.
eapply getparam_abstr => ? ? ?.
admit.
Qed.

End parametricity.
*)