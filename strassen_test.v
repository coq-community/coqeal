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

Instance AD : add A := +%R.
Instance AB : sub A := AlgOp.subr.
Instance AM : mul A := *%R.
Instance A0 : zero A := 0%R.
Instance A1 : one A := 1%R.
Instance mxAD : hadd (matrix A) := (fun m n => +%R).
Instance mxAB : hsub (matrix A) := (fun _ _ M N => M - N ).
Instance mxAM : hmul (matrix A) := @mulmx A.
Instance mxAC : hcast (matrix A) := @castmx A.
Instance ul : ulsub (matrix A) := @matrix.ulsubmx A.
Instance ur : ursub (matrix A) := @matrix.ursubmx A.
Instance dl : dlsub (matrix A) := @matrix.dlsubmx A.
Instance dr : drsub (matrix A) := @matrix.drsubmx A.
Instance blk : block (matrix A) := @matrix.block_mx A.

(* HACK *)
Hint Extern 1000 (param _ _ _) =>
  by rewrite !paramE; do ?[move->|move=>?] : typeclass instances.

Typeclasses Transparent AlgOp.subr.

Goal Strassen (M + N + M + N + M + N + N + M + N)
   (M + N + M + N + M + N + N + M + N) = 
(P *m M + P *m N + P *m M + P *m N + 
 P *m M + P *m N + P *m N + P *m M + P *m N).
Proof.
apply/eqP.
set (x := Strassen _ _ == _).
evar (y : bool).
have : (param Logic.eq x y).
  do ?[eapply param_apply; tc].
  eapply refines_Strassen with (RmxA := @Rseqmx _); tc.
move/param_eq ->.
by compute.
Qed.

(* Definition Strassen_seqmx p := (Strassen (mxA := hseqmatrix A) (p := p)). *)
(*
Eval cbv delta[Strassen_seqmx Strassen] beta zeta in Strassen_seqmx.
*)

End Strassen_seqmx.
