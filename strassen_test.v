(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements.

Require Import ssrint binnat binint seqmatrix strassen.

Section Strassen_seqmx.

Open Scope ring_scope. 

Local Coercion nat_of_pos : positive >-> nat.

Definition M := \matrix_(i,j < (2%positive)) (1:int).
Definition N := \matrix_(i,j < (2%positive)) (2:int).
Definition P := \matrix_(i,j < (2%positive)) (14:int).

Import Refinements.Op.

Notation A := int_Ring.

Instance : hadd (matrix A) := @addmx A.
Instance : hsub (matrix A) := (fun _ _ M N => addmx M (oppmx N)).
Instance : hmul (matrix A) := @mulmx A.
Instance : hcast (matrix A) := @castmx A.
Instance : ulsub (matrix A) := @matrix.ulsubmx A.
Instance : ursub (matrix A) := @matrix.ursubmx A.
Instance : dlsub (matrix A) := @matrix.dlsubmx A.
Instance : drsub (matrix A) := @matrix.drsubmx A.
Instance : block (matrix A) := @matrix.block_mx A.


Goal Strassen (M + N + M + N + M + N + N + M + N)
   (M + N + M + N + M + N + N + M + N) = 
(P *m M + P *m N + P *m M + P *m N + 
 P *m M + P *m N + P *m N + P *m M + P *m N).
Proof.
apply/eqP.
Set Typeclasses Debug.
rewrite [_ == _]RboolE.
by compute.
Qed.

(* Definition Strassen_seqmx p := (Strassen (mxA := hseqmatrix A) (p := p)). *)
(*
Eval cbv delta[Strassen_seqmx Strassen] beta zeta in Strassen_seqmx.
*)

End Strassen_seqmx.
