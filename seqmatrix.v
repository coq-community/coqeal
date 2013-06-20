(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset fingroup perm ssralg bigop matrix mxalgebra.
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

Arguments zipwith {_ _ _} _ _ _.

Lemma param_zipwith A A' (rA : A -> A' -> Prop)
      B B' (rB : B -> B' -> Prop) C C' (rC : C -> C' -> Prop): 
  (getparam (rA ==> rB ==> rC) ==> getparam (seq_hrel rA) ==>
    getparam (seq_hrel rB) ==> getparam (seq_hrel rC))%rel zipwith zipwith.
Proof.
rewrite !paramE => f f' rf.
elim => [|a sa iha] [|a' sa'] //= [ra rsa].
move => [|b sb] [|b' sb'] //= [rb rsb].
by split; [exact: rf|exact: iha].
Qed.

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

Arguments param_zipwith {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Hint Extern 1 (getparam _ _ _) =>
  eapply param_zipwith : typeclass_instances.
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

Import Refinements.Op.
  
Variable A : Type.

(* Definition of seqmatrix and basic combinators *)

Definition seqmatrix := seq (seq A).

Notation hseqmatrix := (fun (_ _ : nat) => seqmatrix).

Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Definition mkseqmx_ord m n (f : 'I_m -> 'I_n -> A) : seqmatrix :=
  let enum_n := ord_enum_eq n in
  map (fun i => map (f i) enum_n) (ord_enum_eq m).

Lemma ord_enum_eqE p : ord_enum_eq p = enum 'I_p.
Proof. by rewrite enumT unlock; apply:eq_pmap ; exact:insub_eqE. Qed.

(* Fake arguments are required because of the type of map_mx *)
Definition map_seqmx (f : A -> A) (* (m n : nat) *) (M : seqmatrix) : seqmatrix :=
  map (map f) M.

Definition zipwithseqmx (f : A -> A -> A) (M N : seqmatrix) : seqmatrix:=
  zipwith (zipwith f) M N.

Definition trseqmx (M : seqmatrix) : seqmatrix :=
  foldr (zipwith cons) (nseq (size (nth [::] M 0)) [::]) M.

Definition const_seqmx m n (x : A) := nseq m (nseq n x).

Section seqmx_block.

Variables m m1 m2 n n1 n2 : nat.

Definition usubseqmx (M : seqmatrix) :=
  take m1 M.

Definition dsubseqmx (M : seqmatrix) :=
  drop m1 M.

Definition lsubseqmx (M : seqmatrix) :=
  map (take n1) M.

Definition rsubseqmx (M : seqmatrix) :=
  map (drop n1) M.

Definition ulsubseqmx (M : seqmatrix) :=
  lsubseqmx (usubseqmx M).

Definition ursubseqmx (M : seqmatrix) :=
  rsubseqmx (usubseqmx M).

Definition dlsubseqmx (M : seqmatrix) :=
  lsubseqmx (dsubseqmx M).

Definition drsubseqmx (M : seqmatrix) :=
  rsubseqmx (dsubseqmx M).

Definition row_seqmx (M N : seqmatrix) : seqmatrix :=
  zipwith cat M N.

Definition col_seqmx (M N : seqmatrix) : seqmatrix :=
  M ++ N.

Definition block_seqmx Aul Aur Adl Adr : seqmatrix :=
  col_seqmx (row_seqmx Aul Aur) (row_seqmx Adl Adr).

End seqmx_block.

Global Instance hulsubseqmx : ulsub hseqmatrix :=
  fun m1 m2 n1 n2 => ulsubseqmx m1 n1.
Global Instance hursubseqmx : ursub hseqmatrix :=
  fun m1 m2 n1 n2 => ursubseqmx m1 n1.
Global Instance hdlsubseqmx : dlsub hseqmatrix :=
  fun m1 m2 n1 n2 => dlsubseqmx m1 n1.
Global Instance hdrsubseqmx : drsub hseqmatrix :=
  fun m1 m2 n1 n2 => drsubseqmx m1 n1.

Global Instance hblock_seqmx : block hseqmatrix :=
  fun _ _ _ _ Aul Aur Adl Adr => block_seqmx Aul Aur Adl Adr.

Global Instance castseqmx : hcast hseqmatrix := fun _ _ _ _ _ M => M.

(* Definition of operations, using an abstract base type and operations *)

Section seqmx_ops.
Import Refinements.Op.
Context `{zero A, opp A, add A, sub A, mul A, eq A}.

Global Instance oppseqmx : @hopp nat hseqmatrix :=
   fun _ _ => map_seqmx -%C.
Global Instance addseqmx : @hadd nat hseqmatrix :=
   fun _ _ => zipwithseqmx +%C.
Global Instance subseqmx : @hsub nat hseqmatrix :=
   fun _ _ => zipwithseqmx sub_op.

Global Instance haddseqmx : hadd hseqmatrix :=
  fun _ _ => zipwithseqmx +%C.
Global Instance hsubseqmx : hsub hseqmatrix :=
  fun _ _ => zipwithseqmx sub_op.

Fixpoint eq_seq T f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

(* Try to inline to see if higher order style hurts performance *)
Global Instance eq_seqmx : @heq nat hseqmatrix :=
  fun _ _ => eq_seq (eq_seq eq_op).

Global Instance heq_seqmx : heq hseqmatrix := fun _ _ => eq_seq (eq_seq eq_op).

Global Instance seqmx0 : hzero hseqmatrix := fun m n => const_seqmx m n 0%C.

Global Instance mulseqmx : @hmul nat hseqmatrix :=
  fun _ n p M N => 
    let N := trseqmx N in
    if n is O then seqmx0 (size M) p else
      map (fun r => map (foldl2 (fun z x y => (x * y) + z) 0 r)%C N) M.

Global Instance scaleseqmx : scale A seqmatrix :=
  fun x M => map_seqmx (mul_op x) M.

Global Instance scalar_seqmx (n : nat) : cast_class A seqmatrix :=
  fun x => @mkseqmx_ord n n (fun i j => if i == j then x else 0%C).

Definition swap (T : Type) m1 m2 (x : T) (s : seq T) :=
  let r := set_nth x s m1 (nth x s m2) in
  set_nth x r m2 (nth x s m1).

Definition xrowseqmx i j (M : seqmatrix) : seqmatrix :=
  swap i j [::] M.

Definition xcolseqmx i j (M : seqmatrix) : seqmatrix :=
  [seq swap i j 0%C s | s <- M].

Definition row_perm_seqmx m (s : nat -> nat) (M : seqmatrix) : seqmatrix :=
  mkseq (fun i => nth [::] M (s i)) m.

End seqmx_ops.

End seqmx.

(***********************************************************)
(* PART II: Proving the properties of the previous objects *)
(***********************************************************)
(* Stating that seqmatrix refines 'M_(_, _) *)

Section seqmx2.

Variable A : Type.

Local Notation seqmatrix := (seqmatrix A).

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

Definition Rseqmx {m n} := ofun_hrel (mx_of_seqmx m n).

(* TODO: there should be an equivalent in refinements *)
Lemma refinesP {m n} {x y : 'M[A]_(m,n)} {a : seqmatrix}
  `{ref_xa : !param Rseqmx x a} : x = y -> Rseqmx y a.
Proof.
by move=> eq_xy; move: ref_xa; rewrite eq_xy paramE.
Qed.

(* Basic refinement properties *)

Section refines_size.

Variables (m n : nat) (M : 'M[A]_(m, n)) (N : seqmatrix).

Context `{ref_MN : !param Rseqmx M N}.

Lemma refines_row_size : size N = m.
Proof.
move: ref_MN.
by rewrite paramE /Rseqmx /mx_of_seqmx /ofun_hrel; have [->|] := altP eqP.
Qed.

Lemma refines_all_col_size : all (fun x => size x == n) N.
Proof.
move: ref_MN.
by rewrite paramE /Rseqmx /mx_of_seqmx /ofun_hrel; have [] := eqP; case: all.
Qed.

Lemma refines_nth_col_size : forall i, i < size N -> size (nth [::] N i) = n.
Proof. by have /(all_nthP [::]) /(_ _ _) /eqP := refines_all_col_size. Qed.

Definition sizeE :=
  (ord_enum_eqE, size_enum_ord, refines_row_size, refines_all_col_size, refines_nth_col_size,
   size_zip, size_map, size_nseq, size_cat, minnn).

End refines_size.

Lemma refines_nth_def m n (M : 'M_(m, n)) (N : seqmatrix) (i : 'I_m) (j : 'I_n) x0 :
  param Rseqmx M N -> nth x0 (nth [::] N i) j = M i j.
Proof.
move=> rMN; move: (rMN).
rewrite paramE /Rseqmx /mx_of_seqmx /ofun_hrel.
case: ifP=> // _; case: ifP=> // _.
rewrite (omap_funoptE (fun ij : 'I_m * 'I_n => nth x0 (nth [::] N ij.1) ij.2)) //=.
+ by move=> [<-]; rewrite mxE.
+ by move=> g g' eq_gg'; apply/matrixP=> k l; rewrite !mxE eq_gg'.
by case=> k l; rewrite (nth_map [::]) /= ?(nth_map x0) ?sizeE.
Qed.

Lemma refines_nth  m n (M : 'M_(m, n)) (N : seqmatrix) (i : 'I_m) (j : 'I_n) :
  param Rseqmx M N -> nth (M i j) (nth [::] N i) j = M i j.
Proof. exact: refines_nth_def. Qed.

Lemma refines_seqmxP m n (x : 'M_(m,n)) (a : seqmatrix) :
  size a = m -> (forall i, i < m -> size (nth [::] a i) = n) ->
  (forall (i:'I_m) (j:'I_n), nth (x i j) (nth [::] a i) j = x i j) ->
  Rseqmx x a.
Proof.
move=> eq_sz eq_row_sz eq_nth.
rewrite /Rseqmx /mx_of_seqmx /ofun_hrel eq_sz eqxx.
rewrite (introT (all_nthP [::])); last first.
by move=> i lt_i_sz; apply/eqP/eq_row_sz; rewrite -eq_sz.
rewrite (omap_funoptE (fun ij => x ij.1 ij.2)) => [|g g' eq_gg'|[i j]].
+ by congr Some; apply/matrixP=> i j; rewrite !mxE.
+ by apply/matrixP=> i j; rewrite !mxE.
by rewrite (nth_map [::]) ?eq_sz //= (nth_map (x i j)) ?eq_row_sz ?eq_nth.
Qed.

Global Instance refines_mkseqmx_ord_tt m n (f : 'I_m -> 'I_n -> A) :
  param Rseqmx (matrix_of_fun tt f) (mkseqmx_ord f).
Proof.
rewrite paramE.
apply/refines_seqmxP=> [|i lt_im|i j].
+ by rewrite size_map ord_enum_eqE size_enum_ord.
+ rewrite (nth_map (Ordinal lt_im)) ?ord_enum_eqE ?size_enum_ord // size_map.
  by rewrite size_enum_ord.
by rewrite !mxE (nth_map i) ?sizeE // (nth_map j) ?sizeE // !nth_ord_enum.
Qed.

Global Instance refines_mkseqmx_ord_mx_key m n (f : 'I_m -> 'I_n -> A) :
  param Rseqmx (matrix_of_fun matrix_key f) (mkseqmx_ord f).
Proof.
rewrite paramE.
apply/refines_seqmxP=> [|i lt_im|i j].
+ by rewrite size_map ord_enum_eqE size_enum_ord.
+ rewrite (nth_map (Ordinal lt_im)) ?ord_enum_eqE ?size_enum_ord // size_map.
  by rewrite size_enum_ord.
by rewrite !mxE (nth_map i) ?sizeE // (nth_map j) ?sizeE // !nth_ord_enum.
Qed.

Definition map_mx_wrapper {A B} (m n : nat) (f : A -> B) (M : 'M_(m,n)) :=
  map_mx f M.

(* We should probably be more parametric here, refining f : R -> R to f : A -> A *)
(* TODO: I don't know how to state this lemma *)
Global Instance refines_map_seqmx m n :
param (Logic.eq ==> Rseqmx ==> Rseqmx) (@map_mx_wrapper A A m n)
  (@map_seqmx A).
Proof.
rewrite paramE => f _ <- x a rxa.
apply/refines_seqmxP=> [|i lt_im|i j].
+ by rewrite !sizeE.
+ by rewrite (nth_map [::]) !sizeE.
rewrite !mxE (nth_map [::]) ?sizeE //.
by rewrite (nth_map (x i j)) ?sizeE // refines_nth.
Qed.

Definition zipwithmx m n (f : A -> A -> A) (M N : 'M[A]_(m,n)) :=
  \matrix_(i,j) f (M i j) (N i j).

Global Instance refines_zipwithseqmx m n :
  param (eq ==> Rseqmx ==> Rseqmx ==> Rseqmx) (@zipwithmx m n) (@zipwithseqmx A).
Proof.
rewrite paramE => f ? <- x a ref_xa y b ?.
rewrite /zipwithseqmx zipwithE; apply/refines_seqmxP=> [|i lt_im|i j].
+ by rewrite !sizeE.
+ by rewrite (nth_map ([::],[::])) ?zipwithE !sizeE // nth_zip !sizeE.
rewrite !mxE (nth_map ([::],[::])) ?zipwithE ?nth_zip ?sizeE //.
by rewrite (nth_map (x i j, y i j)) ?nth_zip ?sizeE // !refines_nth /=.
Qed.

Lemma size_trseqmx {m n} {x : 'M[A]_(m.+1, n)} {a : seqmatrix}
  `{xa : !param Rseqmx x a} : size (trseqmx a) = n.
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
  `{xa : !param Rseqmx x a} i :
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
Global Instance refines_trseqmx m n :
  param (Rseqmx ==> Rseqmx) (@trmx A m.+1 n) (@trseqmx A).
Proof.
rewrite paramE.
move=> x a ref_xa /=.
rewrite /Rseqmx /ofun_hrel /mx_of_seqmx size_trseqmx eqxx.
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
Global Instance refines_const_seqmx m n :
  param (eq ==> Rseqmx) (@const_mx A m n) (const_seqmx m n).
Proof.
rewrite paramE => x x' <-.
rewrite /Rseqmx /ofun_hrel /mx_of_seqmx size_nseq eqxx.
have [_|/(all_nthP [::]) hN] := boolP (all _ _); last first.
  suff: False by [].
  by apply: hN => i; rewrite nth_nseq size_nseq => ->; rewrite size_nseq.
rewrite /= (omap_funoptE (fun ij => x)) => [|g g' eq_gg'|a].
+ by congr Some; apply/matrixP=> i j; rewrite !mxE.
+ by apply/matrixP; move=> i j; rewrite !mxE eq_gg'.
by rewrite (nth_map [::]) /= ?(nth_map x) ?(nth_nseq,ltn_ord,size_nseq).
Qed.

Global Instance refines_xrowseqmx m n :
  param (eq ==> eq ==> Rseqmx ==> Rseqmx) (@xrow A m n) (@xrowseqmx A).
Proof.
rewrite paramE => i i' <- j j' <- x a ref_xa.
apply/refines_seqmxP=> [|k Hk|k l].
+ by rewrite !size_set_nth !(elimT maxn_idPr) ?sizeE.
+ rewrite nth_set_nth /= nth_set_nth /=.
  case: ifP=> _; first by rewrite !sizeE.
  by case: ifP=> _; rewrite !sizeE.
rewrite !mxE nth_set_nth /= nth_set_nth /=.
have [eq_kj | neq_kj] := altP (k =P j);
have [eq_ki | neq_ki] := altP (k =P i).
+ by rewrite -eq_kj eq_ki eqxx tperm1 perm1 refines_nth.
+ by rewrite eq_kj eqxx tpermR refines_nth.
+ rewrite /eqtype.eq_op /= in neq_kj.
+ by rewrite (negbTE neq_kj) eq_ki eqxx tpermL refines_nth.
rewrite /eqtype.eq_op /= in neq_kj neq_ki.
rewrite (negbTE neq_kj) (negbTE neq_ki).
by rewrite tpermD 1?eq_sym // refines_nth.
Qed.

Section seqmx_block.

Variables m m1 m2 n n1 n2 : nat.

Global Instance refines_usubseqmx :
  param (Rseqmx ==> Rseqmx) (@usubmx A m1 m2 n) (usubseqmx m1).
Proof.
rewrite paramE /usubseqmx => x a ref_xa; apply/refines_seqmxP=> [|i Hi|i j].
+ rewrite size_take sizeE; case:m2=> [|p] ; first by rewrite addn0 ltnn.
  by rewrite addnS leq_addr.
+ by rewrite nth_take // !sizeE //; exact:ltn_addr.
by rewrite nth_take // mxE -{2}refines_nth.
Qed.

Global Instance refines_dsubseqmx :
  param (Rseqmx ==> Rseqmx) (@dsubmx A m1 m2 n) (dsubseqmx m1).
Proof.
rewrite paramE /dsubseqmx => x a ref_xa; apply/refines_seqmxP=> [|i Hi|i j].
+ by rewrite size_drop sizeE addKn.
+ by rewrite nth_drop // ?sizeE // ltn_add2l.
by rewrite nth_drop // mxE -{2}refines_nth.
Qed.

Global Instance refines_lsubseqmx :
  param (Rseqmx ==> Rseqmx) (@lsubmx A m n1 n2) (lsubseqmx n1).
Proof.
rewrite paramE /lsubseqmx => x a ref_xa; apply/refines_seqmxP=> [|i Hi|i j].
+ by rewrite size_map sizeE.
+ rewrite (nth_map [::]) ?sizeE // size_take !sizeE //.
  case:n2=> [|p]; first by rewrite addn0 ltnn.
  by rewrite addnS leq_addr.
+ rewrite (nth_map [::]) ?sizeE //.
by rewrite nth_take // mxE -{2}refines_nth.
Qed.

Global Instance refines_rsubseqmx :
  param (Rseqmx ==> Rseqmx) (@rsubmx A m n1 n2) (rsubseqmx n1).
Proof.
rewrite paramE /rsubseqmx => x a ref_xa; apply/refines_seqmxP=> [|i Hi|i j].
+ by rewrite size_map sizeE.
+ rewrite (nth_map [::]) ?sizeE // size_drop.
  by rewrite !sizeE // addKn.
+ rewrite (nth_map [::]) ?sizeE //.
by rewrite nth_drop // mxE -{2}refines_nth.
Qed.

End seqmx_block.

Arguments refines_usubseqmx {m1 m2 n}.
Arguments refines_dsubseqmx {m1 m2 n}.
Arguments refines_lsubseqmx {m n1 n2}.
Arguments refines_rsubseqmx {m n1 n2}.

Section seqmx_block2.

Variables m m1 m2 n n1 n2 : nat.

Global Instance refines_ulsubseqmx :
  param (Rseqmx ==> Rseqmx) (@ulsubmx A m1 m2 n1 n2) (ulsubseqmx m1 n1).
Proof.
rewrite /ulsubmx /ulsubseqmx /= paramE => x a ref_xa.
by rewrite -[Rseqmx]paramE; tc.
Qed.

Global Instance refines_ursubseqmx :
  param (Rseqmx ==> Rseqmx) (@ursubmx A m1 m2 n1 n2) (ursubseqmx m1 n1).
Proof.
rewrite /ursubmx /ursubseqmx /= paramE => x a ref_xa.
by rewrite -[Rseqmx]paramE; tc.
Qed.

Global Instance refines_dlsubseqmx :
  param (Rseqmx ==> Rseqmx) (@dlsubmx A m1 m2 n1 n2) (dlsubseqmx m1 n1).
Proof.
rewrite /dlsubmx /dlsubseqmx /= paramE => x a ref_xa.
by rewrite -[Rseqmx]paramE; tc.
Qed.

Global Instance refines_drsubseqmx :
  param (Rseqmx ==> Rseqmx) (@drsubmx A m1 m2 n1 n2) (drsubseqmx m1 n1).
Proof.
rewrite /drsubmx /drsubseqmx /= paramE => x a ref_xa.
by rewrite -[Rseqmx]paramE; tc.
Qed.

Global Instance refines_row_seqmx :
  param (Rseqmx ==> Rseqmx ==> Rseqmx) (@row_mx A m n1 n2) (@row_seqmx A).
Proof.
rewrite paramE => x a ref_xa y b ref_yb.
apply/refines_seqmxP=> [|i Hi|i j].
+ by rewrite /row_seqmx zipwithE !sizeE.
+ by rewrite /row_seqmx zipwithE (nth_map ([::],[::])) ?nth_zip ?sizeE.
rewrite /row_seqmx zipwithE (nth_map ([::],[::])) ?nth_zip ?sizeE //= nth_cat.
by rewrite !sizeE // mxE; case: splitP => j' ->; rewrite ?addKn refines_nth.
Qed.

Global Instance refines_col_seqmx :
  param (Rseqmx ==> Rseqmx ==> Rseqmx) (@col_mx A m1 m2 n) (@col_seqmx A).
Proof.
rewrite paramE => x a ref_xa y b ref_yb.
apply/refines_seqmxP=> [|i Hi|i j].
+ by rewrite size_cat !sizeE.
+ rewrite nth_cat !sizeE.
  have [lt_im1|leq_m1i] := ltnP i m1.
    by rewrite !sizeE.
  rewrite !sizeE // -(addKn m1 m2); apply: ltn_sub2r => //; case: m2 Hi => [|m2' Hi].
    by rewrite addn0 ltnNge leq_m1i.
  exact: (leq_ltn_trans leq_m1i).
by rewrite nth_cat sizeE mxE; case: splitP => i' ->; rewrite ?addKn refines_nth.
Qed.

End seqmx_block2.

Section seqmx_block3.

Variables m1 m2 n1 n2 : nat.

Global Instance refines_block_seqmx :
  param (Rseqmx ==> Rseqmx ==> Rseqmx ==> Rseqmx ==> Rseqmx)
    (@block_mx A m1 m2 n1 n2) (@block_seqmx A).
Proof.
rewrite paramE => ? ? ref_ul ? ? ref_ur ? ? ref_dl ? ? ref_dr.
rewrite /block_mx /block_seqmx.
rewrite -[Rseqmx]paramE.
by tc.
Qed.

Global Instance refines_cast_seqmx (p : (m1 = m2) * (n1 = n2)) :
  param (Rseqmx ==> Rseqmx) (castmx p) id | 100.
Proof. 
rewrite paramE => ? ?; case: p=> e1 e2.
by case: _ / e1; case: _ / e2.
Qed.

End seqmx_block3.

End seqmx_raw_refinement.
End seqmx2.

Arguments Rseqmx {A m n} _ _.

Section seqmx_eqtype_refinement.
Import Refinements.

Import Refinements.Op.

Variable A : eqType.

Local Instance eq_A : Op.eq A := eqtype.eq_op.

Lemma eq_seqE (T : Type) (f : T -> T -> bool) s1 s2 : size s1 = size s2 ->
  eq_seq f s1 s2 = all (fun xy => f xy.1 xy.2) (zip s1 s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs] [] //= x2 s2 /eqP eq_sz.
by rewrite IHs //; apply/eqP.
Qed.

Global Instance refines_eqseqmx m n :
  param (Rseqmx ==> Rseqmx ==> Logic.eq)
        (eqtype.eq_op : 'M[A]_(m,n) -> _ -> _)
        (@Op.heq_op _ (fun _ _ => seqmatrix A) _ m n).
Proof.
apply param_abstr2 => x a rx y b ry; rewrite paramE. (* ; congr Some. *)
rewrite /Op.heq_op /heq_seqmx /eq_seqmx eq_seqE ?sizeE //.
case: m x y rx ry => [|m] x y rx ry.
  rewrite [a]size0nil ?sizeE // [b]size0nil ?sizeE //.
  by apply/eqP/matrixP; case.
case: n x y rx ry=> [|n] x y rx ry.
  rewrite /Op.eq_op /eq_seqmx.
  have->: x = y by apply/matrixP=> i; case.
  rewrite eqxx; apply/esym/(all_nthP ([::],[::])) => j.
  by rewrite nth_zip !sizeE //= => lt_jm; rewrite 2![nth _ _ _]size0nil ?sizeE.
case: (altP (all_nthP ([::],[::]))).
  rewrite !sizeE => Hi; apply/eqP/matrixP=> i j; move: (Hi i (ltn_ord i)).
  rewrite eq_seqE ?nth_zip ?sizeE //; move/(all_nthP (x i j, y i j)).
  rewrite !sizeE //; move/(_ j (ltn_ord j)).
  by rewrite nth_zip ?sizeE //= !refines_nth; apply/eqP.
pose x0 := x 0 0.
rewrite -has_predC; case/(has_nthP ([::],[::]))=> i; rewrite !sizeE => lt_im /=.
rewrite eq_seqE nth_zip ?sizeE // -has_predC; case/(has_nthP (x 0 0, x 0 0))=> j.
rewrite nth_zip !sizeE //= => lt_jn /eqP neq_ab; apply/eqP/matrixP.
by move/(_ (Ordinal lt_im) (Ordinal lt_jn)); rewrite -2!(refines_nth_def _ _ x0).
Qed.

End seqmx_eqtype_refinement.

Typeclasses Opaque matrix_of_fun const_mx map_mx.

(* Commutative group related refinement properties *)
Section seqmx_zmod_refinement.
Import Refinements.
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
Lemma refines_col_size {m n} {M : 'M_(m, n)} {N : seqmatrix A}
  `{!param Rseqmx M N} : forall x, x \in N -> size x = n.
Proof.
move=> x in_xN; rewrite -(nth_index [::] in_xN).
by rewrite sizeE // index_mem.
Qed.

(* It is not clear that this lemma is better than refines_nth, which applies to *)
(* arbitrary types *)
Lemma refines_mxE {m n} {M : 'M_(m, n)} {N : seqmatrix A}
  `{rMN : !param Rseqmx M N} : M = \matrix_(i, j) (nth [::] N i)`_j.
Proof.
have := rMN; rewrite paramE /Rseqmx /ofun_hrel zmod_mx_of_seqmxE.
by rewrite sizeE // eqxx; have [_ []|/all_nthP hN] := boolP (all _ _).
Qed.

Local Instance zero_A : Op.zero A := 0%R.
Local Instance opp_A : Op.opp A := -%R.
Local Instance add_A : Op.add A := +%R.
Local Instance sub_A : Op.sub A := (fun x y => x - y)%R.

(* This helps automation a bit *)
Local Instance param_eq_refl T (x : T) : param eq x x.
Proof. by rewrite paramE. Qed.

Local Instance param_fun_eq A B (f f' : A -> B) :
  param eq f f' -> param (eq ==> eq) f f'.
Proof.
by rewrite !paramE => <- {f'} x x' <-.
Qed.

Global Instance refines_oppseqmx m n :
  param (Rseqmx ==> Rseqmx) (-%R : 'M[A]_(m,n) -> 'M[A]_(m,n))
        (@Op.hopp_op _ (fun _ _ => seqmatrix A) _ m n).
Proof.
apply param_abstr => x a rxa; rewrite paramE /Op.opp_op /oppseqmx.
have->: -x = map_mx_wrapper -%R x.
  by apply/matrixP=> i j; rewrite !mxE.
rewrite -[Rseqmx]paramE.
rewrite /Op.hopp_op /= /Op.opp_op /opp_A /=.
by tc.
Qed.

Global Instance refines_addseqmx m n :
  param (Rseqmx ==> Rseqmx ==> Rseqmx)
    (+%R : 'M[A]_(m,n) -> 'M[A]_(m,n) -> 'M[A]_(m, n))
    (@Op.hadd_op _ (fun _ _ => seqmatrix A) _ m n).
Proof.
apply param_abstr2 => x a rxa y b ryb; rewrite paramE.
have->: x + y = zipwithmx +%R x y by apply/matrixP=> i j; rewrite !mxE.
rewrite -[Rseqmx]paramE /Op.hadd_op /haddseqmx.
by tc.
Qed.

Global Instance refines_subseqmx m n :
  param (Rseqmx ==> Rseqmx ==> Rseqmx)
    (AlgOp.subr : _ -> _ -> 'M[A]_(m,n))
    (@Op.hsub_op _ (fun _ _ => seqmatrix A) _ m n).
Proof.
apply param_abstr2 => x a rxa y b ryb; rewrite paramE.
have->: AlgOp.subr x y = zipwithmx AlgOp.subr x y.
  by apply/matrixP=> i j; rewrite !mxE.
rewrite -[Rseqmx]paramE /Op.hsub_op /hsubseqmx /Op.sub_op /sub_A.
rewrite /AlgOp.subr.
by tc.
Qed.

(* We use zero as a default element here, but we could relax the zmodType constraint *)
Global Instance refines_xcolseqmx m n :
  param (eq ==> eq ==> Rseqmx ==> Rseqmx)
        (@xcol _ m n) (@xcolseqmx _ _).
Proof.
apply param_abstr2 => i i' ri j j' rj.
move: ri rj; rewrite {1 2}paramE => [[<-] [<-]] {i' j'}.
apply param_abstr => x a rxa; rewrite paramE.
apply/refines_seqmxP=> [|k Hk|k l].
+ by rewrite size_map sizeE.
+ by rewrite (nth_map [::]) ?sizeE // !size_set_nth !(elimT maxn_idPr) ?sizeE.
rewrite (nth_map [::]) ?sizeE //.
rewrite /swap (set_nth_default 0%C) ?size_set_nth ?(elimT maxn_idPr) ?sizeE //.
rewrite nth_set_nth /= nth_set_nth /= !mxE.
have [eq_lj | neq_lj] := altP (l =P j);
have [eq_li | neq_li] := altP (l =P i).
+ by rewrite -eq_lj eq_li eqxx tperm1 perm1 refines_nth_def.
+ by rewrite eq_lj eqxx tpermR refines_nth_def.
+ rewrite /eqtype.eq_op /= in neq_lj.
+ by rewrite (negbTE neq_lj) eq_li eqxx tpermL refines_nth_def.
rewrite /eqtype.eq_op /= in neq_lj neq_li.
rewrite (negbTE neq_lj) (negbTE neq_li).
by rewrite tpermD 1?eq_sym // refines_nth_def.
Qed.

End seqmx_zmod_refinement.

(* Ring related refinement properties *)
Section seqmx_ring_refinement.
Import Refinements.
Variable (A : ringType).

Existing Instances zero_A add_A param_eq_refl.
Local Instance mul_A : Op.mul A := *%R.

Global Instance refines_seqmx0 m n : param Rseqmx (0 : 'M[A]_(m,n)) (seqmx0 m n).
Proof. 
by rewrite /seqmx0 /GRing.zero /= /Op.zero_op /zero_A; tc.
Qed.

Lemma minSS (p q : nat) : minn p.+1 q.+1 = (minn p q).+1.
Proof. by rewrite /minn ltnS; case:ifP. Qed.

Global Instance refines_mulseqmx m n p : 
  param (Rseqmx ==> Rseqmx ==> Rseqmx)
        (mulmx : 'M[A]_(m, n) -> 'M[A]_(n, p) -> _)
        (@Op.hmul_op _ (fun _ _ => seqmatrix A) _ m n p).
Proof.
apply param_abstr2 => x a xa y b yb; rewrite paramE /Op.hmul_op /mulseqmx.
case: n x y xa yb=> [|n] x y xa yb.
  by rewrite thinmx0 mul0mx /mulseqmx sizeE -[Rseqmx]paramE; tc.
rewrite /Rseqmx /ofun_hrel zmod_mx_of_seqmxE.
rewrite size_map sizeE eqxx.
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
have->: y k j = y^T j k by rewrite mxE.
by rewrite [x]refines_mxE [y^T]refines_mxE !mxE.
Qed.

Existing Instance param_fun_eq.

Global Instance refines_scaleseqmx m n :
  param (eq ==> Rseqmx ==> Rseqmx)
        (@GRing.scale _ _ : _ -> 'M[A]_(m, n)  -> _)
        (@Op.scale_op A (seqmatrix A) _).
Proof.
apply param_abstr2 => x x' rx M M' rM; rewrite paramE.
apply/refines_seqmxP=> [|i Hi|i j].
  by rewrite !sizeE.
  by rewrite /Op.scale_op /scaleseqmx !sizeE.
rewrite mxE (nth_map [::]) ?(nth_map x) ?sizeE //.
by move: rx; rewrite refines_nth_def paramE => <-.
Qed.

Global Instance refines_scalar_seqmx n (x : A) :
  param Rseqmx (@scalar_mx _ n x) (scalar_seqmx n x).
Proof.
rewrite paramE; apply/refinesP/matrixP=> i j; rewrite !mxE.
by have [] := altP (i =P j).
Qed.

(* Global Instance refines_matrix m n : *)
(*   param ((refines_id ==> refines_id ==> refines_id) ==> refines) *)
(*         (@matrix_of_fun A m n matrix_key) (@mkseqmx_ord A m n). *)
(* Proof. *)
(* apply param_abstr => f f' rf; rewrite paramE. *)
(* apply/refinesP/matrixP=> i j; rewrite !mxE. *)
(* have [ri rj] : (param refines_id i i * param refines_id j j)%type by rewrite !paramE. *)
(* by rewrite [f i j]param_eq. *)
(* Qed. *)

End seqmx_ring_refinement.

Typeclasses Opaque matrix_of_fun const_mx map_mx mulmx.

(*****************************************)
(* PART III: Parametricity (coming soon) *)
(*****************************************)

Section seqmx_parametricity.
Import Refinements.Op.

Context (A : Type) (C : Type) (rAC : A -> C -> Prop).
Definition RseqmxA {m n} := (@Rseqmx A m n \o (seq_hrel (seq_hrel rAC)))%rel.

Global Instance RseqmxA_map_seqmx m n :
  param ((rAC ==> rAC) ==> RseqmxA ==> RseqmxA)
        (@map_mx_wrapper A A m n) (@map_seqmx C).
Proof. exact: param_trans. Qed.

Global Instance RseqmxA_trseqmx m n :
  param (RseqmxA ==> RseqmxA) (@trmx A m.+1 n) (@trseqmx C).
Proof. exact: param_trans. Qed.

End seqmx_parametricity.

Section seqmx_ring_parametricity.
Import Refinements.Op.

Context (A : ringType) (C : Type) (rAC : A -> C -> Prop).
Notation RseqmxA := (RseqmxA rAC).
Context `{zero C, one C, opp C, add C, sub C, mul C, eq C}.

Context `{!param rAC 0%R 0%C, !param rAC 1%R 1%C}.
Context `{!param (rAC ==> rAC) -%R -%C}.
Context `{!param (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!param (rAC ==> rAC ==> rAC) subr sub_op}.
Context `{!param (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!param (rAC ==> rAC ==> Logic.eq) eqtype.eq_op eq_op}.

Global Instance RseqmxA_oppseqmx m n :
  param (RseqmxA ==> RseqmxA) (-%R : 'M[A]_(m,n) -> 'M[A]_(m,n))
        (@hopp_op _ (fun _ _ => seqmatrix C) _ m n).
Proof. exact: param_trans. Qed.

End seqmx_ring_parametricity.

