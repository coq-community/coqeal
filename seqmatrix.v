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

Section zipwith.
Variables (T1 T2 R : Type) (f : T1 -> T2 -> R).

Fixpoint zipwith (s1 : seq T1) (s2 : seq T2) :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then f x1 x2 :: zipwith s1' s2' else [::]
  else [::].

Lemma zipwithE s1 s2 : zipwith s1 s2 = [seq f x.1 x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x1 s1 ihs1] [|x2 s2] //=; rewrite ihs1. Qed.

End zipwith.

Section oextract.

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

End oextract.
Arguments funoptPn {A B f} a _.
Arguments omap_funoptE {A B C f} g _ _ _.

Section seqmx_def.
Variable A : Type.

Definition seqmatrix := seq (seq A).

Definition mx_of_seqmx m n (M : seqmatrix) : option 'M_(m,n) :=
  if size M == m then
    if all (fun x => size x == n) M
    then let aux (i : 'I_m) (j : 'I_n) := 
             obind (fun l => nth None (map some l) j) (nth None (map some M) i)
         in omap (fun P => \matrix_(i,j) P (i, j)) (funopt (fun ij => aux ij.1 ij.2))
    else None
  else None.

Definition seqmx_of_mx m n (M : 'M[A]_(m,n)) : seqmatrix :=
  [seq [seq (M i j)%C | j <- enum 'I_n] | i <- enum 'I_m].
 
Lemma seqmx_of_mxK m n : pcancel (@seqmx_of_mx m n) (@mx_of_seqmx m n).
Proof.
move=> M; rewrite /seqmx_of_mx /mx_of_seqmx /=.
rewrite size_map /= size_enum_ord eqxx.
set hM := (all _ _); have -> : hM; rewrite /hM.
  by elim: (enum ('I_m)) => //= a s ->; rewrite size_map size_enum_ord eqxx.
rewrite (omap_funoptE (fun ij => M ij.1 ij.2)) /=.
  by congr Some; apply/matrixP=> i j; rewrite mxE.
  by move=> g g' eq_gg' /=; apply/matrixP=> i j; rewrite !mxE.
move=> [i j] /=.
rewrite (nth_map [::]) /=; last by rewrite size_map -cardT card_ord.
rewrite (nth_map (M i j)).
    rewrite (nth_map i); last by rewrite -cardT card_ord.
    rewrite (nth_map j); last by rewrite -cardT card_ord.
  by rewrite !nth_ord_enum.
rewrite (nth_map i); last by rewrite -cardT card_ord.
by rewrite size_map -cardT card_ord.
Qed.

Global Program Instance refinement_mx_seqmx m n :
  refinement 'M[A]_(m,n) seqmatrix := Refinement (@seqmx_of_mxK m n).

Lemma refines_row_size m n (M : 'M_(m, n)) (N : seqmatrix) : 
  refines M N -> size N = m.
Proof.
rewrite /refines /= /mx_of_seqmx //.
by have [->|] := altP eqP.
Qed.


Lemma refines_col_size m n (M : 'M_(m, n)) (N : seqmatrix) : 
  refines M N -> forall i, i < size N -> size (nth [::] N i) = n.
Proof. 
rewrite /refines /= /mx_of_seqmx //; have [sN|//] := altP eqP.
have [hN _|//] := boolP (all _ _) => {M}.
elim: N m sN hN => //= s N ihN [//|m] [sN] /andP [/eqP hs hN].
by move=> [|u]; rewrite ltnS => hu //=; rewrite (ihN m).
Qed.

End seqmx_def.

Section seqmx_zmod.

Variable A : zmodType.

Definition zmod_mx_of_seqmx m n (M : seqmatrix A) : option 'M_(m,n) :=
  if size M == m then
    if all (fun x => size x == n) M
    then some (\matrix_(i, j) (nth [::] M i)`_j)
    else None
  else None.

Lemma mx_of_seqmxE m n (M : seqmatrix A) :
  mx_of_seqmx m n M = zmod_mx_of_seqmx m n M.
Proof.
rewrite /mx_of_seqmx /zmod_mx_of_seqmx; do ![case: ifP=> //=] => hm /eqP hn.
rewrite (omap_funoptE (fun ij : 'I_m * 'I_n => (nth [::] M ij.1)`_ij.2)) //=.
  by move=> g g' eq_g; apply/matrixP => i j; rewrite !mxE.
move=> [i j] /=; rewrite (nth_map [::]) ?hn //= (nth_map 0) //.
by move/allP in hm; rewrite (eqP (hm _ _)) // mem_nth ?hn.
Qed.

Lemma refines_all_row_size m n (M : 'M_(m, n)) (N : seqmatrix A) : 
  refines M N -> forall x, x \in N -> size x = n.
Proof.
rewrite /refines /= /mx_of_seqmx; have [sN|//] := altP eqP.
by case: ifP => // /allP hN _ x xN; rewrite (eqP (hN _ _)).
Qed.

Lemma refines_mxE m n (M : 'M_(m, n)) (N : seqmatrix A) :
  refines M N -> M = \matrix_(i, j) (nth [::] N i)`_j.
Proof.
move=> rMN; have := rMN; rewrite /refines /= mx_of_seqmxE /zmod_mx_of_seqmx.
rewrite refines_row_size // eqxx.
have [_ [] //|/allP hN] := boolP (all _ _).
suff: False by []; apply: hN => x xN.
by apply/eqP; rewrite refines_all_row_size.
Qed.

End seqmx_zmod.

Section seqmx_op.

Variable (A : Type).

Definition zipwithseqmx (M N : seqmatrix A) (f : A -> A -> A) : seqmatrix A :=
  zipwith (zipwith f) M N.

Definition addseqmx `{add A} (M N : seqmatrix A) : seqmatrix A :=
  zipwithseqmx M N +%C.

Global Program Instance add_seqmatrix `{add A} : add (seqmatrix A) := addseqmx.

Definition trseqmx (M : seqmatrix A) : seqmatrix A :=
  foldr (zipwith cons) (nseq (size (nth [::] M 0)) [::]) M.

End seqmx_op.

Section seqmx_op2.

Variable (B : zmodType).

Instance add_B : add B := +%R.

Global Instance refines_addseqmx m n (x y : 'M[B]_(m,n)) (a b : seqmatrix B) 
  (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Proof.
rewrite /add_op /add_seqmatrix /addseqmx /zipwithseqmx /= !zipwithE.
rewrite /refines [x]refines_mxE [y]refines_mxE /=.
rewrite mx_of_seqmxE /zmod_mx_of_seqmx /=.
have [sa sb sab] : [/\ size a = m, size b = m & size (zip a b) = m].
  by rewrite ?size_zip ?refines_row_size ?minnn.
rewrite size_map // sab.
have [_|/allP hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => s /(nthP [::]) [i].
  rewrite size_map sab => hi <-.
  rewrite (nth_map ([::],[::])) ?size_map ?sab //.
  rewrite zipwithE size_map size_zip nth_zip ?refines_row_size //=.
  by rewrite !refines_col_size ?minnn ?(sa, sb).
rewrite eqxx; congr Some; apply/matrixP=> i j; rewrite !mxE.
rewrite (nth_map ([::],[::])) ?sab //=.
rewrite nth_zip ?(sa, sb) //= zipwithE.
rewrite (nth_map (0, 0)) ?size_zip ?refines_col_size ?sa ?sb ?minnn //=.
by rewrite nth_zip ?refines_col_size ?sa ?sb ?minnn.
Qed.

Lemma size_trseqmx m n (x : 'M[B]_(m.+1, n)) (a : seqmatrix B)
  (xa : refines x a) : size (trseqmx a) = n.
Proof.
rewrite /trseqmx.
pose P (s : seqmatrix B) k := forall i, i < size s -> size (nth [::] s i) = k.
have H: forall s1 s2, P s2 (size s1) -> size (foldr (zipwith cons) s1 s2) = size s1.
  move=> s1; elim=> // t s2 IHs H.
  rewrite /= zipwithE size_map size_zip IHs ?(H 0%N) ?minnn //.
  by move=> i Hi; rewrite -(H i.+1).
rewrite H size_nseq refines_col_size // ?refines_row_size //.
by move=> i Hi; rewrite refines_col_size.
Qed.

Lemma size_nth_trseqmx m n (x : 'M[B]_(m.+1, n)) (a : seqmatrix B)
  (xa : refines x a) i :
  i < n -> size (nth [::] (trseqmx a) i) = m.+1.
Proof.
have H: forall k (s1 s2 : seqmatrix B) , k < size (foldr (zipwith cons) s1 s2) -> k < size s1 ->
size (nth [::] (foldr (zipwith cons) s1 s2) k) = (size s2 + size (nth [::] s1 k))%N.
  move=> k s1; elim=> // t s2 IHs /=.
  rewrite !zipwithE size_map=> lt_k_szip lt_k_ss1.
  rewrite (nth_map (0,[::])) //= nth_zip_cond lt_k_szip /= IHs //.
  by move: lt_k_szip; rewrite size_zip leq_min; case/andP.
move=> Hi; rewrite H.
+ by rewrite refines_col_size refines_row_size // nth_nseq Hi.
+ by rewrite size_trseqmx.
by rewrite size_nseq refines_col_size // refines_row_size.
Qed.

Global Instance refines_trseqmx m n (x : 'M[B]_(m.+1,n)) (a : seqmatrix B) 
  (xa : refines x a) : refines (trmx x) (trseqmx a).
Proof.
rewrite /refines [x]refines_mxE /= mx_of_seqmxE /zmod_mx_of_seqmx /=.
rewrite size_trseqmx eqxx.
have [_|/allP hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => s /(nthP [::]) [i].
  by rewrite size_trseqmx=> Hi <-; rewrite size_nth_trseqmx.
congr Some; apply/matrixP=> i j; rewrite !mxE.
have ->: forall (s2 : seqmatrix B) k l s1, k < size (foldr (zipwith cons) s1 s2) ->
 nth 0 (nth [::] (foldr (zipwith cons) s1 s2) k) l =
  if l < size s2 then nth 0 (nth [::] s2 l) k else nth 0 (nth [::] s1 k) (l - size s2).
    elim=> [k l s1|t2 s2 IHs k l s1]; first by rewrite subn0.
    rewrite /= zipwithE size_map=> Hk.
    rewrite (nth_map (0,[::])) //= nth_zip_cond Hk /=.
    by case: l=> //= l; rewrite IHs //; move: Hk; rewrite size_zip leq_min; case/andP.
by rewrite refines_row_size ltn_ord.
by rewrite size_trseqmx.
Qed.

End seqmx_op2.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint seqpoly. *)

(* Eval compute in seqmx0 2 2 : seqmatrix Z. *)
(* Eval compute in seqmx0 2 2 : seqmatrix (seqpoly (seqpoly Z)). *)
(* Eval compute in 1%C : seqmatrix (seqpoly (seqpoly Z)).  *)

