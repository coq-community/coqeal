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

Lemma refines_all_col_size m n (M : 'M_(m, n)) (N : seqmatrix) : 
  refines M N -> all (fun x => size x == n) N.
Proof. by rewrite /refines /= /mx_of_seqmx; have [] := eqP; case: all. Qed.

Lemma refines_nth_col_size m n (M : 'M_(m, n)) (N : seqmatrix) : 
  refines M N -> forall i, i < size N -> size (nth [::] N i) = n.
Proof. by move=> /refines_all_col_size /(all_nthP [::]) /(_ _ _) /eqP. Qed.

End seqmx_def.

Section seqmx_zmod.

Variable A : zmodType.

Lemma zmod_mx_of_seqmxE m n (M : seqmatrix A) :
  mx_of_seqmx m n M =  if size M == m then
                         if all (fun x => size x == n) M
                         then some (\matrix_(i, j) (nth [::] M i)`_j)
                         else None
                       else None.
Proof.
rewrite /mx_of_seqmx; do ![case: ifP=> //=] => hm /eqP hn.
rewrite (omap_funoptE (fun ij : 'I_m * 'I_n => (nth [::] M ij.1)`_ij.2)) //=.
  by move=> g g' eq_g; apply/matrixP => i j; rewrite !mxE.
move=> [i j] /=; rewrite (nth_map [::]) ?hn //= (nth_map 0) //.
by move: hm => /all_nthP /(_ _ _) /eqP ->; rewrite // hn.
Qed.

Lemma refines_col_size m n (M : 'M_(m, n)) (N : seqmatrix A) : 
  refines M N -> forall x, x \in N -> size x = n.
Proof. by move=> /refines_all_col_size /allP /(_ _ _) /eqP. Qed.

Lemma refines_mxE m n (M : 'M_(m, n)) (N : seqmatrix A) :
  refines M N -> M = \matrix_(i, j) (nth [::] N i)`_j.
Proof.
move=> rMN; have := rMN; rewrite /refines /= zmod_mx_of_seqmxE.
rewrite refines_row_size // eqxx.
by have [_ []|/all_nthP hN] := boolP (all _ _).
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

Definition const_seqmx m n (x : A) := nseq m (nseq n x).

Lemma refines_const_seqmx m n x : refines (@const_mx _ m n x) (const_seqmx m n x).
Proof.
rewrite /refines /=.
rewrite /mx_of_seqmx.
rewrite size_nseq eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => i; rewrite size_nseq => lt_i_s.
  by rewrite nth_nseq lt_i_s size_nseq.
rewrite /= (omap_funoptE (fun ij => x)) => [|g g' eq_gg'|a].
+ by congr Some; apply/matrixP=> i j; rewrite !mxE.
+ by apply/matrixP; move=> i j; rewrite !mxE eq_gg'.
by rewrite (nth_map [::]) /= ?(nth_map x) ?(nth_nseq,ltn_ord,size_nseq).
Qed.

Definition seqmx0 `{zero A} m n := const_seqmx m n 0%C.

Fixpoint foldl2 T1 T2 T3 (f : T3 -> T1 -> T2 -> T3) z (s : seq T1) (t : seq T2) {struct s} :=
  if s is x :: s' then
    if t is y :: t' then foldl2 f (f z x y) s' t' else z
  else z.

Definition mulseqmx `{zero A} `{add A} `{mul A} (n p : nat) (M N : seqmatrix A) : seqmatrix A :=
  let N := trseqmx N in
  if n is O then seqmx0 (size M) p else
  map (fun r => map (foldl2 (fun z x y => (x * y) + z) 0 r)%C N) M.

End seqmx_op.

Section seqmx_op2.

Variable (B : zmodType).

Instance zero_B : zero B := 0%R.
Instance add_B : add B := +%R.

Global Instance refines_addseqmx m n (x y : 'M[B]_(m,n)) (a b : seqmatrix B) 
  (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Proof.
rewrite /add_op /add_seqmatrix /addseqmx /zipwithseqmx /= !zipwithE.
rewrite /refines [x]refines_mxE [y]refines_mxE /= zmod_mx_of_seqmxE.
have [sa sb sab] : [/\ size a = m, size b = m & size (zip a b) = m].
  by rewrite ?size_zip ?refines_row_size ?minnn.
rewrite size_map // sab eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => i; rewrite size_map sab => hi.
  rewrite (nth_map ([::],[::])) ?size_map ?sab //.
  rewrite zipwithE size_map size_zip nth_zip ?refines_row_size //=.
  by rewrite !refines_nth_col_size ?minnn ?(sa, sb).
congr Some; apply/matrixP=> i j; rewrite !mxE.
rewrite (nth_map ([::],[::])) ?sab //=.
rewrite nth_zip ?(sa, sb) //= zipwithE.
rewrite (nth_map (0, 0)) ?size_zip ?refines_nth_col_size ?sa ?sb ?minnn //=.
by rewrite nth_zip ?refines_nth_col_size ?sa ?sb ?minnn.
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
rewrite H size_nseq refines_nth_col_size // ?refines_row_size //.
by move=> i Hi; rewrite refines_nth_col_size.
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
+ by rewrite refines_nth_col_size refines_row_size // nth_nseq Hi.
+ by rewrite size_trseqmx.
by rewrite size_nseq refines_nth_col_size // refines_row_size.
Qed.

Global Instance refines_trseqmx m n (x : 'M[B]_(m.+1,n)) (a : seqmatrix B) 
  (xa : refines x a) : refines (trmx x) (trseqmx a).
Proof.
rewrite /refines [x]refines_mxE /= zmod_mx_of_seqmxE /=.
rewrite size_trseqmx eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => i.
  by rewrite size_trseqmx => /size_nth_trseqmx ->.
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

Lemma refines_seqmx0 m n : refines (0 : 'M[B]_(m,n)) (seqmx0 m n).
Proof. exact: refines_const_seqmx. Qed.

End seqmx_op2.

Section seqmx_op3.

Variable (C : ringType).

Instance zero_C : zero C := 0%R.
Instance add_C : add C := +%R.
Instance mul_C : mul C := *%R.

Lemma refines_mulseqmx p m n (x : 'M_(m,p)) (y : 'M_(p,n)) (a b : seqmatrix C)
  (xa : refines x a) (xb : refines y b) : refines (x *m y) (mulseqmx p n a b).
Proof.
(*
rewrite /mulseqmx.
case: ifP => [/eqP hn0 | hn].
- move: M N; rewrite hn0 => M N.
  by rewrite flatmx0 thinmx0 mul0mx size_seqmx seqmx0E.
case: p hn M N => [ | p] //= => _ M N.
apply/seqmxP; split => [|i Hi|i j]; first by rewrite size_map size_seqmx.
  rewrite /rowseqmx (nth_map [::]) size_map.
    by rewrite size_trseqmx.
  by rewrite size_enum_ord.
rewrite /mulseqmx mxE /fun_of_seqmx /rowseqmx (nth_map [::]).
  rewrite (nth_map [::]); last by rewrite size_trseqmx.
  set F := (fun z x y => _); rewrite trseqmxE /seqmx_of_mx.
  case: m i M => [|m' i M]; first by case.
  case: n j N => [|n' j N]; first by case.
  rewrite (nth_map 0) ?size_enum_ord //.
  rewrite (nth_map (0 : 'I_n'.+1)) ?size_enum_ord //.
  have->: forall z, foldl2 F z
     [seq trans (M (enum 'I_m'.+1)`_i j0) |  j0 <- enum 'I_(p.+1)]
     [seq trans (N^T (enum 'I_n'.+1)`_j j0) |  j0 <- enum 'I_(p.+1)] =
  foldl2 (fun z x y => add (mul (trans x) (trans y)) z) z
  [seq M i j0 | j0 <- enum 'I_(p.+1)]  [seq N^T j i0 | i0 <- enum 'I_(p.+1)].
   by elim:(enum 'I_(p.+1))=> // a s IHs /= z; rewrite IHs /= !nth_ord_enum.
  rewrite -zeroE.
  have ->: forall s1 s2 (x : R),
    (foldl2 (fun z x y => add (mul (trans x) (trans y)) z) (trans x) s1 s2) =
    trans (x + \sum_(0 <= k < minn (size s1) (size s2)) s1`_k * s2`_k).
    move=>t; elim=>[s2 x|t1 s1 IHs s2 x].
      by rewrite min0n big_mkord big_ord0 GRing.addr0.
    case:s2=>[|t2 s2]; first by rewrite minn0 big_mkord big_ord0 GRing.addr0.
    by rewrite /= -mulE -addE IHs minSS big_nat_recl [_ + x]GRing.addrC GRing.addrA.
  rewrite GRing.add0r size_map size_enum_ord size_map size_enum_ord minnn big_mkord.
  congr trans; apply:eq_bigr=>k _; rewrite (nth_map 0) ?size_enum_ord //.
  rewrite [X in _ * X](nth_map (0 : 'I_p.+1)) ?size_enum_ord // mxE.
  by rewrite nth_ord_enum.
by rewrite size_seqmx.
*)
admit.
Qed.

End seqmx_op3.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint seqpoly. *)

(* Eval compute in seqmx0 2 2 : seqmatrix Z. *)
(* Eval compute in seqmx0 2 2 : seqmatrix (seqpoly (seqpoly Z)). *)
(* Eval compute in 1%C : seqmatrix (seqpoly (seqpoly Z)).  *)

