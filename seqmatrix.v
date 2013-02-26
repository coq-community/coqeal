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

(********************************************************)
(* Preamble: a few additions from the libraries we use. *)
(********************************************************)

Section preamble.
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

(* Could be made more precise to avoid proving matrix_of_fun g = matrix_of_fun g' each time *)
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
End preamble.
Arguments funoptPn {A B f} a _.
Arguments omap_funoptE {A B C f} g _ _ _.


Section extra_seq.

Fixpoint foldl2 T1 T2 T3 (f : T3 -> T1 -> T2 -> T3) z (s : seq T1) (t : seq T2) {struct s} :=
  if s is x :: s' then
    if t is y :: t' then foldl2 f (f z x y) s' t' else z
  else z.

End extra_seq.

(*************************************************************)
(* PART I: Definiting datastructures and programming with it *)
(*************************************************************)

Section seqmx.
Variable A : Type.

(* Definition of seqmatrix and basic combinators *)

Definition seqmatrix := seq (seq A).

Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Definition mkseqmx_ord m n (f : 'I_m -> 'I_n -> A) : seqmatrix :=
  let enum_n := ord_enum_eq n in
  map (fun i => map (f i) enum_n) (ord_enum_eq m).

Definition map_seqmx (f : A -> A) (M : seqmatrix) : seqmatrix :=
  map (map f) M.

Definition zipwithseqmx (f : A -> A -> A) (M N : seqmatrix) : seqmatrix:=
  zipwith (zipwith f) M N.

Definition trseqmx (M : seqmatrix) : seqmatrix :=
  foldr (zipwith cons) (nseq (size (nth [::] M 0)) [::]) M.

Definition const_seqmx m n (x : A) := nseq m (nseq n x).

(* Definition of operations, using an abstract base type and operations *)

Section seqmx_ops.
Context `{zero A, opp A, add A, sub A, mul A, eq A}.

Global Instance opp_seqmatrix : opp seqmatrix := map_seqmx -%C.
Global Instance add_seqmatrix : add seqmatrix := zipwithseqmx +%C.
Global Instance sub_seqmatrix : sub seqmatrix := zipwithseqmx sub_op.

Global Instance eq_seqmatrix : eq seqmatrix := fun M N =>
  foldl2 (fun acc x y => acc && (foldl2 (fun acc x y => acc && eq_op x y) true x y)) true M N.

Definition seqmx0 m n := const_seqmx m n 0%C.

Definition mulseqmx (n p : nat) (M N : seqmatrix) : seqmatrix :=
  let N := trseqmx N in
  if n is O then seqmx0 (size M) p else
  map (fun r => map (foldl2 (fun z x y => (x * y) + z) 0 r)%C N) M.

End seqmx_ops.

(***********************************************************)
(* PART II: Proving the properties of the previous objects *)
(***********************************************************)
(* Stating that seqmatrix refines 'M_(_, _) *)

Section seqmx_raw_refinement.

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
move=> [i j] /=; rewrite (nth_map [::]) ?(size_enum_ord, size_map) //=.
rewrite (nth_map (M i j)) (nth_map i) 1?(nth_map j) ?nth_ord_enum //;
by rewrite ?(size_enum_ord, size_map).
Qed.

Global Program Instance refinement_mx_seqmx m n :
  refinement 'M[A]_(m,n) seqmatrix := Refinement (@seqmx_of_mxK m n).

(* Basic refinement properties *)

Lemma refines_row_size m n (M : 'M_(m, n)) (N : seqmatrix) : 
  refines M N -> size N = m.
Proof. by rewrite /refines /= /mx_of_seqmx //; have [->|] := altP eqP. Qed.

Lemma refines_all_col_size m n (M : 'M_(m, n)) (N : seqmatrix) : 
  refines M N -> all (fun x => size x == n) N.
Proof. by rewrite /refines /= /mx_of_seqmx; have [] := eqP; case: all. Qed.

Lemma refines_nth_col_size m n (M : 'M_(m, n)) (N : seqmatrix) : 
  refines M N -> forall i, i < size N -> size (nth [::] N i) = n.
Proof. by move=> /refines_all_col_size /(all_nthP [::]) /(_ _ _) /eqP. Qed.

Definition sizeE :=
  (refines_row_size, refines_all_col_size, refines_nth_col_size,
   size_zip, size_map, size_nseq, minnn).

Lemma refines_nth  m n (M : 'M_(m, n)) (N : seqmatrix) (i : 'I_m) (j : 'I_n) x0 :
  refines M N -> nth x0 (nth [::] N i) j = M i j.
Proof.
move=> rMN; move: (rMN).
rewrite /refines /= /mx_of_seqmx.
case: ifP=> // _; case: ifP=> // _.
rewrite (omap_funoptE (fun ij : 'I_m * 'I_n => nth x0 (nth [::] N ij.1) ij.2)) //=.
(* Why can't we move/Some_inj ? *)
+ by move=> H; rewrite (Some_inj H) mxE.
+ by move=> g g' eq_gg'; apply/matrixP=> k l; rewrite !mxE eq_gg'.
by case=> k l; rewrite (nth_map [::]) /= ?(nth_map x0) ?sizeE.
Qed.

Global Instance refines_mkseqmx_ord m n tt (f : 'I_m -> 'I_n -> A) :
  refines (matrix_of_fun tt f) (mkseqmx_ord f) | 99.
Proof.
admit.
Qed.

Global Instance refines_map_seqmx m n (x : 'M[A]_(m,n)) (a : seqmatrix) (f : A -> A) :
  refines x a -> refines (map_mx f x) (map_seqmx f a).
Proof.
move=> rxa.
rewrite /refines /= /mx_of_seqmx.
rewrite !sizeE eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by []; apply hN => i; rewrite !sizeE => ltim.
  by rewrite (nth_map [::]) ?sizeE.
rewrite (omap_funoptE (fun ij => f (x ij.1 ij.2))) => [|g g' eq_gg'|[i j]].
+ by congr Some; apply/matrixP=> i j; rewrite !mxE.
+ by apply/matrixP=> i j; rewrite !mxE eq_gg'.
rewrite (nth_map [::]) ?sizeE //= (nth_map (x i j)) (nth_map [::]) ?sizeE //.
by rewrite (nth_map (x i j)) ?sizeE // refines_nth.
Qed.

Global Instance refines_zipwithseqmx m n (x y : 'M[A]_(m,n)) (a b : seqmatrix)
  (f : A -> A -> A) (xa : refines x a) (yb : refines y b) :
  refines (\matrix_(i,j) f (x i j) (y i j)) (zipwithseqmx f a b).
Proof.
rewrite /zipwithseqmx zipwithE /refines /= /mx_of_seqmx ?sizeE // eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => i; rewrite ?sizeE => hi.
  by rewrite (nth_map ([::],[::])) ?(sizeE, nth_zip, zipwithE).
rewrite (omap_funoptE (fun ij => f (x ij.1 ij.2) (y ij.1 ij.2))) => [|g g' eq_gg'|[i j]].
+ by congr Some; apply/matrixP=> i j; rewrite !mxE.
+ by apply/matrixP=> i j; rewrite !mxE.
+ rewrite /= (nth_map [::]) ?sizeE //=.
rewrite ?(nth_map (x i j)) ?(nth_map ([::],[::])) ?zipwithE ?nth_zip ?sizeE //.
by rewrite (nth_map (x i j, x i j)) ?nth_zip ?sizeE // !refines_nth.
Qed.

Lemma size_trseqmx m n (x : 'M[A]_(m.+1, n)) (a : seqmatrix)
  (xa : refines x a) : size (trseqmx a) = n.
Proof.
rewrite /trseqmx.
pose P (s : seqmatrix) k := forall i, i < size s -> size (nth [::] s i) = k.
have H: forall s1 s2, P s2 (size s1) -> size (foldr (zipwith cons) s1 s2) = size s1.
  move=> s1; elim=> // t s2 IHs H.
  rewrite /= zipwithE ?(sizeE, IHs, H 0%N) //.
  by move=> i Hi; rewrite -(H i.+1).
by rewrite H ?sizeE // => i Hi; rewrite sizeE.
Qed.

Lemma size_nth_trseqmx m n (x : 'M[A]_(m.+1, n)) (a : seqmatrix)
  (xa : refines x a) i :
  i < n -> size (nth [::] (trseqmx a) i) = m.+1.
Proof.
suff H: forall k (s1 s2 : seqmatrix) , k < size (foldr (zipwith cons) s1 s2) -> k < size s1 ->
size (nth [::] (foldr (zipwith cons) s1 s2) k) = (size s2 + size (nth [::] s1 k))%N.
  by move=> Hi; rewrite H ?size_trseqmx ?sizeE // nth_nseq Hi.
move=> k s1; elim=> // t s2 IHs /=.
rewrite !zipwithE size_map=> lt_k_szip lt_k_ss1.
move: (lt_k_szip); case: {1}(zip t (foldr (zipwith cons) s1 s2))=> // [] [x0 _] _ _.
rewrite (nth_map (x0,[::])) //= nth_zip_cond lt_k_szip /= IHs //.
by move: lt_k_szip; rewrite sizeE leq_min; case/andP.
Qed.

(* trseqmx refines the proof-oriented trmx *)
Global Instance refines_trseqmx m n (x : 'M[A]_(m.+1,n)) (a : seqmatrix)
  (xa : refines x a) : refines (trmx x) (trseqmx a).
Proof.
rewrite /refines /= /mx_of_seqmx size_trseqmx eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => i.
  by rewrite size_trseqmx => /size_nth_trseqmx ->.
rewrite (omap_funoptE (fun ij => x ij.2 ij.1)) => [|g g' eq_gg'|[i j]].
by congr Some; apply/matrixP=> i j; rewrite !mxE.
by apply/matrixP=> i j; rewrite !mxE eq_gg'.
rewrite (nth_map [::]) ?size_trseqmx //= (nth_map (x j i)) ?size_nth_trseqmx //.
congr Some.
have ->: forall (s2 : seqmatrix) k l s1, k < size (foldr (zipwith cons) s1 s2) ->
 nth (x j i) (nth [::] (foldr (zipwith cons) s1 s2) k) l =
  if l < size s2 then nth (x j i) (nth [::] s2 l) k else nth (x j i) (nth [::] s1 k) (l - size s2).
+ elim=> [k l s1|t2 s2 IHs k l s1]; first by rewrite subn0.
  rewrite /= zipwithE size_map=> Hk.
  rewrite (nth_map (x j i,[::])) //= nth_zip_cond Hk /=.
  by case: l=> //= l; rewrite IHs //; move: Hk; rewrite sizeE leq_min; case/andP.
+ by rewrite sizeE ltn_ord refines_nth.
by rewrite size_trseqmx.
Qed.

(* const_seqmx refines the proof-oriented const_mx *)
Instance refines_const_seqmx m n x : refines (@const_mx _ m n x) (const_seqmx m n x).
Proof.
rewrite /refines /= /mx_of_seqmx size_nseq eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by [].
  by apply: hN => i; rewrite nth_nseq size_nseq => ->; rewrite size_nseq.
rewrite /= (omap_funoptE (fun ij => x)) => [|g g' eq_gg'|a].
+ by congr Some; apply/matrixP=> i j; rewrite !mxE.
+ by apply/matrixP; move=> i j; rewrite !mxE eq_gg'.
by rewrite (nth_map [::]) /= ?(nth_map x) ?(nth_nseq,ltn_ord,size_nseq).
Qed.

End seqmx_raw_refinement.
End seqmx.

Section seqmx_eqtype_refinement.

Variable A : eqType.

Local Instance eq_A : eq A := eqtype.eq_op.

Lemma refines_eqseqmx m n (x y : 'M[A]_(m,n)) (a b : seqmatrix A)
  (rp : refines x a) (rq : refines y b) : (x == y)%R = (a == b)%C.
Proof.
admit.
Qed.

End seqmx_eqtype_refinement.

(* Commutative group related refinement properties *)
Section seqmx_zmod_refinement.
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

(* Pb: rewriting with this lemma can pick wrong instances since the type *)
(* is not determined in the equality. More precisely, neither M nor N appears *)
(* in size x = n. *)
Lemma refines_col_size m n (M : 'M_(m, n)) (N : seqmatrix A) :
  refines M N -> forall x, x \in N -> size x = n.
Proof. by move=> /refines_all_col_size /allP /(_ _ _) /eqP. Qed.

(* It is not clear that this lemma is better than refines_nth, which applies to *)
(* arbitrary types *)
Lemma refines_mxE m n (M : 'M_(m, n)) (N : seqmatrix A) :
  refines M N -> M = \matrix_(i, j) (nth [::] N i)`_j.
Proof.
move=> rMN; have := rMN; rewrite /refines /= zmod_mx_of_seqmxE.
by rewrite sizeE // eqxx; have [_ []|/all_nthP hN] := boolP (all _ _).
Qed.

Local Instance zero_A : zero A := 0%R.
Local Instance opp_A : opp A := -%R.
Local Instance add_A : add A := +%R.
Local Instance sub_A : sub A := (fun x y => x - y)%R.

Global Instance refines_oppseqmx m n (x : 'M[A]_(m,n)) (a : seqmatrix A) 
  (xa : refines x a) : refines (- x)%R (- a)%C.
Proof.
by rewrite /opp_op /opp_seqmatrix; apply/refinesP/matrixP=> i j; rewrite !mxE.
Qed.

Global Instance refines_addseqmx m n (x y : 'M[A]_(m,n)) (a b : seqmatrix A) 
  (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Proof.
by rewrite /add_op /add_seqmatrix; apply/refinesP/matrixP=> i j; rewrite !mxE.
Qed.

Global Instance refines_subseqmx m n (x y : 'M[A]_(m,n)) (a b : seqmatrix A) 
  (xa : refines x a) (yb : refines y b) : refines (x - y)%R (sub_op a b)%C.
Proof.
by rewrite /sub_op /sub_seqmatrix; apply/refinesP/matrixP=> i j; rewrite !mxE.
Qed.

End seqmx_zmod_refinement.

(* Ring related refinement properties *)
Section seqmx_ring_refinement.

Variable (A : ringType).

Existing Instances zero_A add_A.
Local Instance mul_A : mul A := *%R.

(* Instance refines_seqmx0 m n : refines (0 : 'M[A]_(m,n)) (seqmx0 m n). *)
(* Proof. exact: refines_const_seqmx. Qed. *)

Lemma minSS (p q : nat) : minn p.+1 q.+1 = (minn p q).+1.
Proof. by rewrite /minn ltnS; case:ifP. Qed.

Global Instance refines_mulseqmx p m n (x : 'M_(m,p)) (y : 'M_(p,n)) (a b : seqmatrix A)
  (xa : refines x a) (yb : refines y b) : refines (x *m y) (mulseqmx p n a b).
Proof.
case: p x y xa yb=> [|p] x y xa yb.
  rewrite thinmx0 mul0mx /mulseqmx sizeE.
  exact: refines_const_seqmx.
rewrite /refines [x]refines_mxE [y]refines_mxE /= zmod_mx_of_seqmxE.
rewrite !sizeE eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by []; apply: hN => i.
by rewrite size_map => lt_i_sa; rewrite (nth_map [::]) // size_map size_trseqmx.
congr Some.
apply/matrixP=> i j; rewrite !mxE.
rewrite ?(nth_map [::]) ?sizeE //.
set F := (fun z x y => _).
have ->: forall s1 s2 (t : A), (foldl2 F t s1 s2) =
    (t + \sum_(0 <= k < minn (size s1) (size s2)) s1`_k * s2`_k).
  elim=>[s2 t|t1 s1 IHs s2 t].
    by rewrite min0n big_mkord big_ord0 GRing.addr0.
  case:s2=>[|t2 s2]; first by rewrite minn0 big_mkord big_ord0 GRing.addr0.
  by rewrite /= IHs minSS big_nat_recl /F [(_ + t)%C]addrC addrA.
rewrite add0r ?sizeE // big_mkord; apply: eq_bigr=> k _.
by rewrite !mxE !refines_nth mxE.
Qed.

End seqmx_ring_refinement.

(*****************************************)
(* PART III: Parametricity (coming soon) *)
(*****************************************)


(* (* Some tests *) *)
Require Import ZArith ssrint binint seqpoly.

(* Eval compute in seqmx0 2 2 : seqmatrix Z. *)
(* Eval compute in seqmx0 2 2 : seqmatrix (seqpoly (seqpoly Z)). *)
(* Eval compute in 1%C : seqmatrix (seqpoly (seqpoly Z)).  *)

Definition M := \matrix_(i,j < 2) 1%:Z.
Definition N := \matrix_(i,j < 2) 2%:Z.
Definition P := \matrix_(i,j < 2) 14%:Z.

Goal M + N + M + N + M + N + N + M + N = P.
apply/eqP.
rewrite /M /N /P.
rewrite refines_eqseqmx.
reflexivity.
Qed.