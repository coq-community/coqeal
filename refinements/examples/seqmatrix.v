(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset fingroup perm ssralg bigop matrix mxalgebra.
Require Import refinements.

Require Import ZArith ssrint hrel binint seqmatrix.

Require binnat.

Open Scope ring_scope.

Definition M := \matrix_(i,j < 2) 1%num%:Z.
Definition N := \matrix_(i,j < 2) 2%num%:Z.
Definition P := \matrix_(i,j < 2) 14%num%:Z.

Set Typeclasses Debug.

Goal - P = - P.
Proof.
apply/eqP.
erewrite param_eq; last first.
eapply param_apply.
eapply param_apply.

(* We does the following pick the instance binnat.eq_N ? *)
eapply @RseqmxA_eqseqmx.
Abort.

Goal (M + N + M + N + M + N + N + M + N) *m
   (M + N + M + N + M + N + N + M + N) = 
(P *m M + P *m N + P *m M + P *m N + 
 P *m M + P *m N + P *m N + P *m M + P *m N).
Proof.
apply/eqP.
rewrite [_ == _]param_eq.
by compute.
Qed.
