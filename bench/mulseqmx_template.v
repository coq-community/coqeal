(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import Int31 Int31Native Streams.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements seqmatrix strassen ssrint31 random.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope int31_scope.

Definition n := #MXSIZE%N.

Definition S1 := random_mx n n.
Definition S2 := random_mx_rec S1.2 [::] n n.
Definition M := S1.1.
Definition N := S2.1.

Eval native_compute in ignore M.
Eval native_compute in ignore N.

Definition P := @mulseqmx _ _ _ _ n n n M N.
Time Eval native_compute in ignore P.
