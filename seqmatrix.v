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

(*
Lemma funoptPn (A : finType) (B : Type) (f : A -> option B) :
  ~~ (funopt f) -> exists a, ~~ f a.
Proof.
move=> hf; apply/existsP; rewrite -negb_forall; apply/negP.
by move: hf; rewrite /funopt; case: forallP.
Qed.
*)

Lemma funoptPn (A : finType) (B : Type) (f : A -> option B) a :
  f a = None -> funopt f = None.
Proof.
move=> hfa; rewrite /funopt.
by case: forallP=> // hf; move: (hf a); rewrite hfa.
Qed.

Arguments funoptPn {A B f} a _.

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

Lemma seqmx_of_mxK m n : pcancel (@seqmx_of_mx m n) (@mx_of_seqmx m n).
Proof.
move=> M; rewrite /seqmx_of_mx /mx_of_seqmx /=.
rewrite (omap_funoptE (fun ij => M ij.1 ij.2)) /=.
  by congr Some; apply/matrixP=> i j; rewrite mxE.
  by move=> g g' eq_gg' /=; apply/matrixP=> i j; rewrite !mxE.
move=> [i j] /=.
rewrite (nth_map [::]) /=; last by rewrite size_map -cardT card_ord.
rewrite (nth_map (M i j)) /=.
  rewrite (nth_map i); last by rewrite -cardT card_ord.
  rewrite (nth_map j); last by rewrite -cardT card_ord.
  by rewrite !nth_ord_enum.
rewrite (nth_map i); last by rewrite -cardT card_ord.
by rewrite size_map -cardT card_ord.
Qed.

Global Program Instance refinement_mx_seqmx m n :
  refinement 'M[A]_(m,n) seqmatrix := Refinement (@seqmx_of_mxK m n).

(* Is this really wrong? *)
Lemma wrong m (M : 'M[A]_(m,0)) : refines M [::].
Proof.
rewrite /refines.
rewrite /spec /= /mx_of_seqmx (omap_funoptE (fun ij => M ij.1 ij.2)) /=.
  by congr Some; apply/matrixP=> i j; rewrite mxE.
  by move=> g g' eq_gg' /=; apply/matrixP=> i j; rewrite !mxE.
by case=> ? [].
Qed.

(* We may want to enforce dimensions of any seqmatrix to be exactly the same *)
(* as the matrix they refine (for now, they are greater or equal) *)
Lemma size_seqmx m n (M : 'M[A]_(m,n)) M' : refines M M' -> 0 < n -> m <= size M'.
Proof.
move=> ref_MM' lt0n.
move: (@spec_refines _ _ _ _ _ ref_MM').
rewrite /spec /= /mx_of_seqmx.
have [//|lt_sM'm] := leqP m (size M').
rewrite (funoptPn (Ordinal lt_sM'm, Ordinal lt0n)) //.
by rewrite nth_default // size_map.
Qed.

(* Is it really needed to assume i < m ? *)
Lemma size_nth_seqmx m n (M : 'M[A]_(m,n)) M' i x0 :
  refines M M' -> i < m -> n <= size (nth x0 M' i).
Proof.
move=> ref_MM' ltim.
move: (@spec_refines _ _ _ _ _ ref_MM').
rewrite /spec /= /mx_of_seqmx.
have [{14}-> //|lt0n] := posnP n.
have [//|lt_sM'_n] := leqP n (size (nth x0 M' i)).
rewrite (funoptPn (Ordinal ltim, Ordinal lt_sM'_n)) //.
rewrite (nth_map x0).
by rewrite /obind /oapp nth_default // size_map.
by apply/(leq_trans ltim)/size_seqmx.
Qed.

Lemma nth_refines m n (M : 'M[A]_(m,n)) M' (i : 'I_m) (j : 'I_n) x0 x1 :
  refines M M' -> nth x0 (nth x1 M' i) j = M i j.
Proof.
case: n j M => [[]//|n j M].
move=> ref_MM'; move: (ref_MM').
rewrite /refines /spec /= /mx_of_seqmx.
rewrite (omap_funoptE (fun ij : 'I_m * 'I_n.+1 => nth x0 (nth x1 M' ij.1) ij.2)) /=.
move=> H.
by rewrite (Some_inj H) mxE.
by move=> g g' eq_gg'; apply/matrixP=> i' j'; rewrite !mxE eq_gg'.
case=> i' j' /=.
rewrite (nth_map x1) /=.
rewrite (nth_map x0) //.
by apply/(leq_trans (ltn_ord j'))/size_nth_seqmx.
by apply/(leq_trans (ltn_ord i'))/size_seqmx.
Qed.

End seqmx.

Section seqmx_op.

Variable (A : Type).

Definition zipwithseqmx (M N : seqmatrix A) (f : A -> A -> A) : seqmatrix A :=
  zipwith (zipwith f) M N.

Definition addseqmx `{add A} (M N : seqmatrix A) : seqmatrix A :=
  zipwithseqmx M N +%C.

Global Program Instance add_seqmatrix `{add A} : add (seqmatrix A) := addseqmx.

End seqmx_op.

Section seqmx_op2.

Variable (B : zmodType).

Instance add_B : add B := +%R.

Global Program Instance refines_addseqmx m n (x y : 'M[B]_(m,n)) (a b : seqmatrix B) 
  (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Next Obligation.
rewrite /seqmx_of_mx /mx_of_seqmx /=.
rewrite (omap_funoptE (fun ij => (x + y) ij.1 ij.2)) /=.
  by congr Some; apply/matrixP=> i j; rewrite mxE.
  by move=> g g' eq_gg' /=; apply/matrixP=> i j; rewrite !mxE.
move=> [i j] /=.
rewrite (nth_map [::]) /=; last first.
rewrite size_zipwith.
rewrite leq_min.
by apply/andP; split; apply/(leq_trans (ltn_ord i))/size_seqmx; case: n j x xa y yb; case.
rewrite (nth_map 0).
(* rewrite /add_op /add_seqmatrix /addseqmx /zipwithseqmx. *)
congr Some.
rewrite (nth_zipwith _ [::] [::]).
rewrite (nth_zipwith _ 0 0).
rewrite mxE.
congr GRing.add.
by rewrite nth_refines.
by rewrite nth_refines.
rewrite leq_min; apply/andP; split.
fail.

by rewrite size_map -cardT card_ord.
rewrite (nth_map (M i j)) /=.
  rewrite (nth_map i); last by rewrite -cardT card_ord.
  rewrite (nth_map j); last by rewrite -cardT card_ord.
  by rewrite !nth_ord_enum.
rewrite (nth_map i); last by rewrite -cardT card_ord.
by rewrite size_map -cardT card_ord.


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

