(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop matrix mxalgebra.
Require Import ssrcomplements refinements.

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

Definition seqmatrix A := seq (seq A).

Section seqmx.

Variable A : zmodType.

Definition mx_of_seqmx m n (M : seqmatrix A) : option 'M_(m,n) :=
  if size M == m then
    if all (fun x => size x == n) M
    then some (\matrix_(i, j) (nth [::] M i)`_j)
    else None
  else None.
  
Definition seqmx_of_mx m n (M : 'M[A]_(m,n)) : seqmatrix A :=
  [seq [seq (M i j)%C | j <- enum 'I_n] | i <- enum 'I_m].

Lemma seqmx_of_mxK m n : pcancel (@seqmx_of_mx m n) (@mx_of_seqmx m n).
Proof.
move=> M; rewrite /seqmx_of_mx /mx_of_seqmx /=.
rewrite size_map /= size_enum_ord eqxx.
(* case: posnP => [->|_] in M *; first by rewrite thinmx0. *)
case: ifP => [_|]; last first.
  move=> /negbT /allPn => [[x /(nthP [::]) [i hi <-]]] .
  rewrite size_map size_enum_ord in hi.
  rewrite (nth_map (Ordinal hi)) ?size_enum_ord //.
  by rewrite size_map size_enum_ord eqxx.
congr Some; apply/matrixP => i j; rewrite mxE /=.
rewrite (nth_map i) 1?(nth_map j) ?size_enum_ord //.
by congr (M _ _); apply: val_inj; rewrite nth_ord_enum.
Qed.

Global Program Instance refinement_mx_seqmx m n :
  refinement 'M[A]_(m,n) (seqmatrix A) := Refinement (@seqmx_of_mxK m n).

Lemma refines_row_size m n (M : 'M_(m, n)) (N : seqmatrix A) : 
  refines M N -> size N = m.
Proof.
rewrite /refines /= /mx_of_seqmx //.
by have [->|] := altP eqP.
Qed.

Lemma refines_all_row_size m n (M : 'M_(m, n)) (N : seqmatrix A) : 
  refines M N -> forall x, x \in N -> size x = n.
Proof.
rewrite /refines /= /mx_of_seqmx; have [sN|//] := altP eqP.
by case: ifP => // /allP hN _ x xN; rewrite (eqP (hN _ _)).
Qed.

Lemma refines_col_size m n (M : 'M_(m, n)) (N : seqmatrix A) : 
  refines M N -> forall i, i < size N -> size (nth [::] N i) = n.
Proof. by move=> rMN i hi; rewrite refines_all_row_size // mem_nth. Qed.

Lemma refines_mxE m n (M : 'M_(m, n)) (N : seqmatrix A) :
  refines M N -> M = \matrix_(i, j) (nth [::] N i)`_j.
Proof.
move=> rMN; have := rMN; rewrite /refines /= /mx_of_seqmx.
rewrite refines_row_size // eqxx.
have [_ [] //|/allP hN] := boolP (all _ _).
suff: False by []; apply: hN => x xN.
by apply/eqP; rewrite refines_all_row_size.
Qed.

End seqmx.

Section seqmx_op.

Variable (A : Type).

Definition zipwithseqmx (M N : seqmatrix A) (f : A -> A -> A) : seqmatrix A :=
  [seq [seq f x.1 x.2 | x <- zip y.1 y.2] | y <- zip M N].

Definition addseqmx `{add A} (M N : seqmatrix A) : seqmatrix A :=
  zipwithseqmx M N +%C.

Global Program Instance add_seqmatrix `{add A} : add (seqmatrix A) := addseqmx.

End seqmx_op.

Section seqmx_op2.

Variable (B : zmodType).

Instance add_B : add B := +%R.

Global Instance refines_addseqmx m n (x y : 'M[B]_(m,n)) (a b : seqmatrix B) 
  (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Proof.
rewrite /add_op /add_seqmatrix /addseqmx /zipwithseqmx /=.
rewrite /refines [x]refines_mxE [y]refines_mxE /= /mx_of_seqmx /=.
have [sa sb sab] : [/\ size a = m, size b = m & size (zip a b) = m].
  by rewrite ?size_zip ?refines_row_size ?minnn.
rewrite size_map // sab.
have [_|/allP hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => s /(nthP [::]) [i].
  rewrite size_map sab => hi <-.
  rewrite (nth_map ([::],[::])) ?size_map ?sab //.
  rewrite size_zip nth_zip ?refines_row_size //=.
  by rewrite !refines_col_size ?minnn ?(sa, sb).
rewrite eqxx; congr Some; apply/matrixP=> i j; rewrite !mxE.
rewrite (nth_map ([::],[::])) ?sab //=.
rewrite nth_zip ?(sa, sb) //=.
rewrite (nth_map (0, 0)) ?size_zip ?refines_col_size ?sa ?sb ?minnn //=.
by rewrite nth_zip ?refines_col_size ?sa ?sb ?minnn.
Qed.

End seqmx.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint seqpoly. *)

(* Eval compute in seqmx0 2 2 : seqmatrix Z. *)
(* Eval compute in seqmx0 2 2 : seqmatrix (seqpoly (seqpoly Z)). *)
(* Eval compute in 1%C : seqmatrix (seqpoly (seqpoly Z)).  *)

