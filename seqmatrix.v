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

Lemma oextract_subdef A (o : option A) : o -> {a | o = Some a}.
Proof. by case: o => [a|]; first by exists a. Qed.

Definition oextract A (o : option A) (po : o) := projT1 (oextract_subdef po).

Lemma oextractK A (o : option A) (po : o) : Some (oextract po) = o.
Proof. by rewrite /oextract; case: oextract_subdef. Qed.

Lemma oextractE A (o : option A) (a : A) (po : o) : Some a = o -> oextract po = a.
Proof. by move=> hao; apply: Some_inj; rewrite oextractK. Qed.

Definition funopt (A : finType) (B : Type)
           (f : A -> option B) : option (A -> B) := 
  if @forallP _ f is ReflectT P then Some (fun a => oextract (P a)) else None.

Lemma funoptP (A : finType) (B : Type) (f : A -> option B) :
  (forall a, f a) -> forall a, omap (@^~ a) (funopt f) = f a .
Proof. by rewrite /funopt; case: forallP => //= *; rewrite oextractK. Qed.

Lemma funoptPn (A : finType) (B : Type) (f : A -> option B) :
  ~~ (funopt f) -> exists a, ~~ f a.
Proof.
move=> hf; apply/existsP; rewrite -negb_forall; apply/negP.
by move: hf; rewrite /funopt; case: forallP.
Qed.

Definition funopt_prf (A : finType) (B : Type)
  (f : A -> option B) (P : forall a, f a) : forall a, f a :=
  if forallP is ReflectT P' then P' else P.

Lemma funoptE (A : finType) (B : Type) (f : A -> option B) 
  (P : forall a, f a) : funopt f = Some (fun a => oextract (funopt_prf P a)).
Proof. by rewrite /funopt /funopt_prf; case: forallP. Qed.

Lemma omap_funoptE (A : finType) (B C : Type)
      (f : A -> option B) (g : A -> B) (h : (A -> B) -> C):
      (forall g g', g =1 g' -> h g = h g') ->
      (forall a, f a = Some (g a)) -> 
      omap h (funopt f) = Some (h g).
Proof.
move=> Hh Hfg; rewrite funoptE; first by move=> a; rewrite Hfg.
by move=> p /=; congr Some; apply: Hh => a; apply: oextractE.
Qed.
Arguments omap_funoptE {A B C f} g _ _ _.

Section seqmx.

Variable A : Type.

Definition seqmatrix := seq (seq A).

Definition mx_of_seqmx m n (M : seqmatrix) : option 'M_(m,n) :=
  let aux (i : 'I_m) (j : 'I_n) := 
      obind (fun l => nth None (map some l) j) (nth None (map some M) i)
  in omap (fun P => \matrix_(i,j) P (i, j)) (funopt (fun ij => aux ij.1 ij.2)).
  
Definition seqmx_of_mx m n (M : 'M[A]_(m,n)) : seqmatrix :=
  [seq [seq (M i j)%C | j <- enum 'I_n] | i <- enum 'I_m].

Definition seqmx_of_mxK m n : pcancel (@seqmx_of_mx m n) (@mx_of_seqmx m n).
Proof.
move=> M; rewrite /seqmx_of_mx /mx_of_seqmx /=.
rewrite (omap_funoptE (fun ij => M ij.1 ij.2)) /=.
  by congr Some; apply/matrixP=> i j; rewrite mxE.
  by move=> g g' eq_gg' /=; apply/matrixP=> i j; rewrite !mxE.
move=> [i j] /=.
admit.
Qed.


(* Global Program Instance ImplemSeqmx `{Implem A B} m n :  *)
(*   Implem 'M[A]_(m,n) seqmatrix := @seqmx_of_mx _ m n. *)
(* Global Program Instance RefinesSeqmx `{Refines A B} m n :  *)
(*   Refines (ImplemSeqmx m n). *)
(* Obligation 1. admit. Qed. *)

(* Definition const_seqmx m n (x : B) := nseq m (nseq n x). *)

(* Lemma const_seqmxE `{Refines A B} m n x : *)
(*   const_seqmx m n (| x |)%C = (| @const_mx _ m n x |)%C. *)
(* Proof. *)
(* admit. *)
(* Qed. *)

(* Definition seqmx0 `{Zero B} m n := const_seqmx m n 0%C. *)

(* Lemma seqmx0E `{Implem A B, Zero B} m n : (| 0%R : 'M[A]_(m,n) |)%C = seqmx0 m n. *)
(* Proof.  *)
(* rewrite /seqmx0 /=. *)
(* admit. *)
(* Qed. *)

(* Global Program Instance ZeroSeqmx `{Zero B} m n : Zero seqmatrix := seqmx0 m n. *)
(* Global Program Instance ZeroMorphSeqmx `{Implem A B, Zero B} : Morph implem 0 0%C. *)
(* Obligation 1. *)
(* rewrite /implem. *)
(* admit. *)
(* Qed. *)

(* Definition mkseqmx (f : nat -> nat -> B) m n : seqmatrix := *)
(*   mkseq (fun i => mkseq (f i) n) m. *)

(* Definition scalar_seqmx `{Zero B} m n x := *)
(*   mkseqmx (fun i j => if i == j then x else 0%C) m n. *)

(* Definition seqmx1 `{Zero B, One B} m n := scalar_seqmx m n 1%C. *)

(* Global Program Instance OneSeqmx `{Zero B, One B} m : One seqmatrix :=  *)
(*   seqmx1 m m. *)
(* Global Program Instance OneMorphSeqmx `{Refines A B, Zero B, One B} : *)
(*   Morph implem 1 1%C. *)
(* Obligation 1. *)
(* rewrite /implem. *)
(* admit. *)
(* Qed. *)

End seqmx.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint seqpoly. *)

(* Eval compute in seqmx0 2 2 : seqmatrix Z. *)
(* Eval compute in seqmx0 2 2 : seqmatrix (seqpoly (seqpoly Z)). *)
(* Eval compute in 1%C : seqmatrix (seqpoly (seqpoly Z)).  *)

