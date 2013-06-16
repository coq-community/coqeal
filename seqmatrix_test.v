(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset fingroup perm ssralg bigop matrix mxalgebra.
Require Import refinements.

Require Import ZArith ssrint binint seqmatrix.

Open Scope ring_scope.

Definition M := \matrix_(i,j < 2) 1%:Z.
Definition N := \matrix_(i,j < 2) 2%:Z.
Definition P := \matrix_(i,j < 2) 14%:Z.

Goal (M + N + M + N + M + N + N + M + N) *m
   (M + N + M + N + M + N + N + M + N) = 
(P *m M + P *m N + P *m M + P *m N + 
 P *m M + P *m N + P *m N + P *m M + P *m N).
Proof.
apply/eqP.
rewrite [_ == _]RboolE.
by compute.
Qed.
