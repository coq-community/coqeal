Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
Require Import path choice fintype tuple finset ssralg bigop poly matrix.

Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Refinements.Op.

Local Open Scope ring_scope.
Local Open Scope rel.

Delimit Scope hetero_computable_scope with HC.

(* Section classes. *)

(* Class hzero_of {I} B := hzero_op : forall {m n : I}, B m n. *)

(* End classes. *)

(* Notation "0" := hzero_op : hetero_computable_scope. *)

Section seqmx_op.

Variable A B : Type.

Definition seqmx := seq (seq A).

Context `{zero_of A, one_of A, add_of A, opp_of A, eq_of A}.

Definition const_seqmx m n (x : A) := nseq m (nseq n x).
Definition map_seqmx (f : A -> A) (M : seqmx) := map (map f) M. 

Global Instance seqmx0 m n : zero_of seqmx := const_seqmx m n 0%C.
(* Global Instance seqpoly1 : one_of seqpoly := [:: 1]. *)
Global Instance seqmx_opp : opp_of seqmx := map_seqmx -%C.

End seqmx_op.

Parametricity const_seqmx.
Parametricity seqmx0.

Section seqmx_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oppR : opp_of R := -%R.

CoInductive Rseqmx {m n} : 'M[R]_(m,n) -> seqmx R -> Type :=
  Rseqmx_spec (A : 'M[R]_(m,n)) M of
    size M == m
  & all (fun x => size x == n) M
  & [forall ij, (A ij.1 ij.2 == nth 0 (nth [::] M ij.1) ij.2) ] : Rseqmx A M.

Lemma Rseqmx_0 m n : refines Rseqmx (0 : 'M[R]_(m,n)) (seqmx0 m n).
Proof.
rewrite refinesE; constructor; first by rewrite size_nseq.
  apply/(all_nthP [::])=> i; rewrite size_nseq=> him.
  by rewrite nth_nseq him size_nseq.
by apply/forallP=> /= [[i j]] /=; rewrite mxE !(nth_nseq,ltn_ord).
Qed.

Lemma Rseqmx_opp m n : refines (Rseqmx ==> Rseqmx) (-%R : 'M[R]_(m,n) -> 'M[R]_(m,n)) (@seqmx_opp R oppR).
Proof.
rewrite refinesE=> ? ? [A M h1 h2 h3].
constructor; first by rewrite size_map h1.
  apply/(all_nthP [::])=> i; rewrite size_map=> hi.
  by rewrite (nth_map [::]) // size_map (allP h2) //; apply/nthP; exists i.
apply/forallP=> /= [[i j]] /=.
rewrite !mxE.
admit.
Qed.

Section seqmx_param.

End seqmx_param.
End seqmx_theory.



