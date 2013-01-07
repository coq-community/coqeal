(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop matrix mxalgebra.
Require Import refinements.

(******************************************************************************)
(* Lists of lists is a refinement of SSReflect matrices                       *) 
(*                                                                            *)
(* ImplemSeqmx m n  == if B implements A then seqmx B implements 'M[A]_(m,n)  *)
(* RefinesSeqmx m n == if B refines A then seqmx B refines 'M[A]_(m,n)        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.

Section seqmx.

Variable A : ringType.
Variable B : Type.

Definition seqmatrix := seq (seq B).

Definition seqmx_of_mx `{Implem A B} m n (M : 'M[A]_(m,n)) : seqmatrix :=
  [seq [seq (| M i j |)%C | j <- enum 'I_n] | i <- enum 'I_m].

Global Program Instance ImplemSeqmx `{Implem A B} m n : 
  Implem 'M[A]_(m,n) seqmatrix := @seqmx_of_mx _ m n.
Global Program Instance RefinesSeqmx `{Refines A B} m n : 
  Refines (ImplemSeqmx m n).
Obligation 1. admit. Qed.

Definition const_seqmx m n (x : B) := nseq m (nseq n x).

Lemma const_seqmxE `{Refines A B} m n x :
  const_seqmx m n (| x |)%C = (| @const_mx _ m n x |)%C.
Proof.
admit.
Qed.

Definition seqmx0 `{Zero B} m n := const_seqmx m n 0%C.

Lemma seqmx0E `{Implem A B, Zero B} m n : (| 0%R : 'M[A]_(m,n) |)%C = seqmx0 m n.
Proof. 
rewrite /seqmx0 /=.
admit.
Qed.

Global Program Instance ZeroSeqmx `{Zero B} m n : Zero seqmatrix := seqmx0 m n.
Global Program Instance ZeroMorphSeqmx `{Implem A B, Zero B} : Morph implem 0 0%C.
Obligation 1.
rewrite /implem.
admit.
Qed.

Definition mkseqmx (f : nat -> nat -> B) m n : seqmatrix :=
  mkseq (fun i => mkseq (f i) n) m.

Definition scalar_seqmx `{Zero B} m n x :=
  mkseqmx (fun i j => if i == j then x else 0%C) m n.

Definition seqmx1 `{Zero B, One B} m n := scalar_seqmx m n 1%C.

Global Program Instance OneSeqmx `{Zero B, One B} m : One seqmatrix := 
  seqmx1 m m.
Global Program Instance OneMorphSeqmx `{Refines A B, Zero B, One B} :
  Morph implem 1 1%C.
Obligation 1.
rewrite /implem.
admit.
Qed.

End seqmx.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint seqpoly. *)

(* Eval compute in seqmx0 2 2 : seqmatrix Z. *)
(* Eval compute in seqmx0 2 2 : seqmatrix (seqpoly (seqpoly Z)). *)
(* Eval compute in 1%C : seqmatrix (seqpoly (seqpoly Z)).  *)

