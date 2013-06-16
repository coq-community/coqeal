(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements.

Require Import binnat binint seqmatrix strassen.

Section Strassen_seqmx.

Definition Strassen_seqmx p := (Strassen (mxA := hseqmatrix A) (p := p)).



(*
Eval cbv delta[Strassen_seqmx Strassen] beta zeta in Strassen_seqmx.
*)

End Strassen_seqmx.
