(* This file is part of CoqEAL, the Coq Effective Algebra Library *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix ssrcomplements.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section matrix_complements.

Variable R : ringType.

Lemma row_flat_mx (m n : nat) (M : 'M_(m,0)) (N : 'M[R]_(m,n)) :
  row_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case:(splitP j)=> [|k H]; first by case.
by congr fun_of_matrix; exact:val_inj.
Qed.

(*
Lemma row_mx_flat (m n : nat) (M : 'M_(m,n)) (N : 'M[R]_(m,0)) :
  row_mx M N = M.
Proof.
apply/matrixP=> i j; rewrite mxE; case:(splitP j)=> [|k H]; first by case.
by congr fun_of_matrix; exact:val_inj.
Qed.
*)

End matrix_complements.

Section seqmx.

Local Open Scope ring_scope.

Variable mT : ringType.

Section SeqmxDef.

Definition seqmatrix := seq (seq mT).
Definition seqrow := seq mT.

Variables m n : nat.

Definition mkseqmx (f:nat->nat->mT) : seqmatrix :=
  mkseq (fun i => mkseq (fun j => f i j) n) m.

Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Lemma ord_enum_eqE p : ord_enum_eq p = enum 'I_p.
Proof. by rewrite enumT unlock; apply:eq_pmap ; exact:insub_eqE. Qed.

(*
Lemma ord_enumE p : ord_enum p = enum 'I_p.
Proof. by rewrite enumT unlock. Qed.
*)

Definition mkseqmx_ord (f:'I_m->'I_n->mT) : seqmatrix :=
  let enum_n := ord_enum_eq n in
  map (fun i => map (f i) enum_n) (ord_enum_eq m).

Lemma eq_mkseqmx_ord f g :
  f =2 g -> mkseqmx_ord f = mkseqmx_ord g.
Proof. by move=> Hfg; apply:eq_map=> i; apply:eq_map=> j. Qed.

Definition rowseqmx (M : seqmatrix) i := nth [::] M i.

Definition mx_of_seqmx (M:seqmatrix) :=
  \matrix_(i < m, j < n) nth 0%R (rowseqmx M i) j.

Definition fun_of_seqmx (M:seqmatrix) := fun i j => nth 0%R (rowseqmx M i) j.

Coercion fun_of_seqmx : seqmatrix >-> Funclass.

Lemma fun_of_seqmxE (M:seqmatrix) i j : M i j = nth 0%R (nth [::] M i) j.
Proof. by []. Qed.

(*
Lemma seqmxP (M N : seqmatrix) :
  [/\ size M = size N, forall i, i < size M -> size (rowseqmx M i) = size (rowseqmx N i) &
  forall i j, M i j = N i j] <-> M = N.
Proof.
split=> [[H H' HMN]|H].
  apply:(@eq_from_nth _ [::])=> // i Hi.
  apply:(@eq_from_nth _ 0)=> [|j Hj] ; first exact:(H' _ Hi) ; last exact:HMN.
by split => [|i|i j]; rewrite H.
Qed.
*)

Lemma mkseqmxE f i j : i < m -> j < n -> mkseqmx f i j = f i j.
Proof. by move=> Hi Hj ; rewrite /fun_of_seqmx /rowseqmx !nth_mkseq. Qed.

(* For ssreflect >= 1.4 *)
(*
Definition seqmx_of_mx (M:'M_(m,n)) : seqmatrix :=
  [seq [seq M i j | j <- enum 'I_n] | i <- enum 'I_m].
*)

(* For ssreflect 1.3 *)
Definition seqmx_of_mx (M:'M_(m,n)) : seqmatrix :=
  map (fun i => map (fun j => M i j) (enum 'I_n)) (enum 'I_m).

Lemma size_seqmx : forall (M:'M[mT]_(m,n)),
  size (seqmx_of_mx M) = m.
Proof. by move=> M ; rewrite size_map size_enum_ord. Qed.

Lemma seqmxE : forall (M:'M[mT]_(m,n)) (i:'I_m) (j:'I_n),
  (seqmx_of_mx M) i j = M i j.
Proof.
move=> M i j ; rewrite /fun_of_seqmx /rowseqmx.
rewrite (nth_map i); last by rewrite size_enum_ord ltn_ord.
rewrite (nth_map j); last by rewrite size_enum_ord ltn_ord.
by rewrite !nth_ord_enum.
Qed.

End SeqmxDef.

Section Degenerate.

Variables m n : nat.

Lemma seqmx0n (M:'M[mT]_(0,n)) : seqmx_of_mx M = [::].
Proof. by rewrite /seqmx_of_mx (size0nil (size_enum_ord 0)). Qed.

Lemma seqmxm0 (M:'M[mT]_(m,0)) : seqmx_of_mx M = map (fun _ => [::]) (enum 'I_m).
Proof. by rewrite /seqmx_of_mx (size0nil (size_enum_ord 0)). Qed.

End Degenerate.

Section FixedDim.

Variables m n : nat.

Lemma seqmx_eqP (M N : 'M[mT]_(m,n)) :
  reflect (M = N) (seqmx_of_mx M == seqmx_of_mx N).
Proof.
by apply/(iffP idP)=> [H|->//]; apply/matrixP=> i j; rewrite -!seqmxE (eqP H).
Qed.

Lemma size_row_seqmx : forall (M:'M[mT]_(m,n)) i,
  i < m -> size (rowseqmx (seqmx_of_mx M) i) = n.
Proof.
case:m=> [M i|p M i Hi] ; first by rewrite ltn0.
rewrite /rowseqmx (nth_map 0) ; first by rewrite size_map size_enum_ord.
by rewrite size_enum_ord.
Qed.

Lemma size_row_mkseqmx f i : 
  i < m -> size (rowseqmx (mkseqmx m n f) i) = n.
Proof. by move=> Hi ; rewrite /rowseqmx nth_mkseq // size_mkseq. Qed.

Lemma seqmxP (M : seqmatrix) (N : 'M_(m,n)) :
  [/\ m = size M, forall i, i < m -> size (rowseqmx M i) = n &
  forall (i:'I_m) (j:'I_n), M i j = N i j] <-> M = seqmx_of_mx N.
Proof.
split=> [[Hm Hn HMN]|->].
  apply:(@eq_from_nth _ [::])=> [|i Hi] ; first by rewrite size_seqmx.
  rewrite -Hm in Hi ; apply:(@eq_from_nth _ 0)=> [|j] ; rewrite (Hn _ Hi).
    by rewrite size_row_seqmx.
  by move=> Hj; rewrite -!fun_of_seqmxE (HMN (Ordinal Hi) (Ordinal Hj)) -seqmxE.
split=> [|i Hi|i j] ; first by rewrite size_seqmx.
  by rewrite size_row_seqmx.
by rewrite seqmxE.
Qed.

Lemma seqmx_of_funE (f : 'I_m -> 'I_n -> mT) :
  seqmx_of_mx (\matrix_(i < m, j < n) f i j) = mkseqmx_ord f.
Proof.
rewrite /mkseqmx_ord /seqmx_of_mx !ord_enum_eqE.
by apply:eq_map=> i; rewrite enumT unlock; apply:eq_map=> j; rewrite mxE.
Qed.

End FixedDim.

Section SeqmxOp.

Variables m n p' : nat.
Local Notation p := p'.+1.

Definition map2seqmx (M N : seqmatrix) (f : mT -> mT -> mT) : seqmatrix :=
  zipwith (zipwith f) M N.

Lemma map2seqmxE (M N : 'M_(m,n)) (f : mT -> mT -> mT) :
  map2seqmx (seqmx_of_mx M) (seqmx_of_mx N) f = seqmx_of_mx (\matrix_(i < m, j < n) f (M i j) (N i j)).
Proof.
apply/seqmxP ; split=>[|i Hi|i j].
    by rewrite size_zipwith !size_seqmx minnn.
  rewrite /rowseqmx (nth_zipwith _ [::] [::]) ; last by rewrite !size_seqmx minnn.
  by rewrite size_zipwith !size_row_seqmx // minnn.
rewrite fun_of_seqmxE (nth_zipwith _ [::] [::]); last by rewrite !size_seqmx // minnn.
rewrite (nth_zipwith _ 0 0) ; last by rewrite !size_row_seqmx // minnn.
by rewrite -!fun_of_seqmxE !seqmxE mxE.
Qed.

(*
Lemma size_row_map2_seqmx (M : 'M_(m,n)) i :
  size (rowseqmx (seqmx_of_mx M) i) = n.
Proof.
rewrite /rowseqmx /seqmx_of_mx.
 (nth_map2 [::] 0).
*)

Definition addseqmx (M N : seqmatrix) : seqmatrix :=
  map2seqmx M N (fun x y => x + y).

Lemma addseqmxE:
  {morph (@seqmx_of_mx m n) : M N / M + N >-> addseqmx M N}.
Proof. by move=> M N ; rewrite /addseqmx map2seqmxE. Qed.

Definition subseqmx (M N : seqmatrix) :=
  map2seqmx M N (fun x y => x - y).

Lemma subseqmxE:
  {morph (@seqmx_of_mx m n) : M N / M - N >-> subseqmx M N}.
Proof.
move=> M N ; rewrite /subseqmx map2seqmxE.
by congr seqmx_of_mx; apply/matrixP=> i j ; rewrite !mxE.
Qed.

Definition trseqmx (M : seqmatrix) : seqmatrix :=
  foldr (zipwith cons) (nseq (size (rowseqmx M 0)) [::]) M.

(*
Lemma trseqmxE (M : 'M_(m.+1,n.+1)) :
  trseqmx (seqmx_of_mx M) = seqmx_of_mx (trmx M).
Proof.
pose P s k := forall i, i < size s -> size (rowseqmx s i) = k.
have Hn: forall s1 s2, P s2 (size s1) -> size (foldr (map2 cons) s1 s2) = size s1.
  move=> s1; elim=> // t s2 IHs H.
  have Hs2: (P s2 (size s1)).
    by move=> i Hi; move:(H i.+1 Hi); move:(H 1%N (leq_ltn_trans (leq0n i) Hi))=> <-.
  by rewrite size_map2 (IHs Hs2) (H 0%N) // minnn.
have Hm: forall i s1 s2, i < size (foldr (map2 cons) s1 s2) -> i < size s1 ->
size (rowseqmx (foldr (map2 cons) s1 s2) i) = (size s2 + size (rowseqmx s1 i))%N.
  move=> i s1; elim=> // t s2 IHs H1 H2.
  rewrite /rowseqmx (nth_map2 0 [::]).
    by rewrite /= IHs //; move:H1; rewrite size_map2 leq_minr; case/andP.
  by rewrite -(size_map2 cons).
apply/seqmxP ; split => [|i Hi|i j].
  + rewrite Hn size_nseq size_row_seqmx //.
    by move=> i; rewrite size_seqmx=> Hi; rewrite size_row_seqmx.
  + rewrite Hm.
      by rewrite size_seqmx /rowseqmx nth_nseq; case:ifP.
rewrite Hn.
Abort.
*)

Lemma size_trseqmx (M : 'M_(m.+1, n)) : size (trseqmx (seqmx_of_mx M)) = n.
Proof.
rewrite /trseqmx.
pose P s k := forall i, i < size s -> size (rowseqmx s i) = k.
have H: forall s1 s2, P s2 (size s1) -> size (foldr (zipwith cons) s1 s2) = size s1.
  move=> s1; elim=> // t s2 IHs H.
  have Hs2: (P s2 (size s1)).
   by move=> i Hi; move:(H i.+1 Hi); move:(H 1%N (leq_ltn_trans (leq0n i) Hi))=> <-.
  by rewrite size_zipwith (IHs Hs2) (H 0%N) // minnn.
rewrite H size_nseq size_row_seqmx //.
by move=> i; rewrite size_seqmx=> Hi; rewrite size_row_seqmx.
Qed.

Lemma size_row_trseqmx (M : 'M_(m.+1, n)) i :
  i < n -> size (rowseqmx (trseqmx (seqmx_of_mx M)) i) = m.+1.
Proof.
have H: forall k s1 s2, k < size (foldr (zipwith cons) s1 s2) -> k < size s1 ->
size (rowseqmx (foldr (zipwith cons) s1 s2) k) = (size s2 + size (rowseqmx s1 k))%N.
  move=> k s1; elim=> // t s2 IHs H1 H2.
  rewrite /rowseqmx (nth_zipwith _ 0 [::]).
    by rewrite /= IHs //; move:H1; rewrite size_zipwith leq_minr; case/andP.
  by rewrite -(size_zipwith cons).
move=> Hi; rewrite H.
  + by rewrite size_seqmx /rowseqmx nth_nseq; case:ifP.
  + by rewrite size_trseqmx.
  by rewrite size_nseq size_row_seqmx.
Qed.

Lemma trseqmxE (M : 'M_(m.+1, n)) :
  trseqmx (seqmx_of_mx M) = seqmx_of_mx (trmx M).
Proof.
apply/seqmxP; split => [|i Hi|i j].
  + by rewrite size_trseqmx.
  + by rewrite size_row_trseqmx.
rewrite /trseqmx /fun_of_seqmx.
have ->: forall s2 k l s1, k < size (foldr (zipwith cons) s1 s2) ->
 nth 0 (nth [::] (foldr (zipwith cons) s1 s2) k) l =
  if l < size s2 then nth (0:mT) (nth [::] s2 l) k else nth 0 (nth [::] s1 k) (l - size s2).
    elim=> [k l s1|t2 s2 IHs k l s1]; first by rewrite subn0.
    rewrite size_zipwith => Hk; rewrite (nth_zipwith _ 0 [::]) //.
    case:l=> // l; rewrite /= IHs //.
    by rewrite leq_minr in Hk; case/andP:Hk.
  by rewrite size_seqmx ltn_ord mxE -seqmxE.
by rewrite size_trseqmx.
Qed.

End SeqmxOp.

Section SeqmxOp2.

Variables m n p' : nat.
Local Notation p := p'.+1.

Definition mulseqmx (M N: seqmatrix) : seqmatrix :=
  let N := trseqmx N in
  map (fun r => map (foldl2 (fun z x y => x * y + z) 0 r) N) M.

Lemma minSS (p q : nat) : minn p.+1 q.+1 = (minn p q).+1.
Proof. by rewrite /minn ltnS; case:ifP. Qed.

Lemma mulseqmxE (M:'M_(m,p)) (N:'M_(p,n)) :
  mulseqmx (seqmx_of_mx M) (seqmx_of_mx N) = seqmx_of_mx (M *m N).
Proof.
apply/seqmxP; split => [|i Hi|i j]; first by rewrite size_map size_seqmx.
  rewrite /rowseqmx (nth_map [::]) size_map.
    by rewrite size_trseqmx.
  by rewrite size_enum_ord.
rewrite /mulseqmx mxE /fun_of_seqmx /rowseqmx (nth_map [::]).
  rewrite (nth_map [::]); last by rewrite size_trseqmx.
  have-> : forall s1 s2 (x : mT), (foldl2 (fun z x y => x * y + z) x s1 s2) =
    x + \sum_(0 <= k < minn (size s1) (size s2)) s1`_k * s2`_k.
    elim=>[s2 x|t1 s1 IHs s2 x].
      by rewrite min0n big_mkord big_ord0 GRing.addr0.
    case:s2=>[|t2 s2]; first by rewrite minn0 big_mkord big_ord0 GRing.addr0.
    by rewrite /= IHs minSS big_nat_recl [_ + x]GRing.addrC GRing.addrA.
  rewrite GRing.add0r size_row_seqmx // size_row_trseqmx // minnn big_mkord.
  by apply:eq_bigr=>k _; rewrite trseqmxE -!fun_of_seqmxE !seqmxE mxE.
by rewrite size_seqmx.
Qed.

End SeqmxOp2.

Lemma mulseqmxEnn : forall m (M:'M_m) (N:'M_m),
  mulseqmx (seqmx_of_mx M) (seqmx_of_mx N) = seqmx_of_mx (M *m N).
Proof. by case=>[M N|m M N]; rewrite ?(flatmx0 M) ?mul0mx ?seqmx0n ?mulseqmxE. Qed.

Section SeqmxRowCol.

Variables m m1 m2 n n1 n2 : nat.

(* Block operations *)
Definition usubseqmx (M : seqmatrix) :=
  take m1 M.

Definition dsubseqmx (M : seqmatrix) :=
  drop m1 M.

Definition lsubseqmx (M : seqmatrix) :=
  map (take n1) M.

Definition rsubseqmx (M : seqmatrix) :=
  map (drop n1) M.

Lemma usubseqmxE : forall (M:'M[mT]_(m1+m2,n)),
  usubseqmx (seqmx_of_mx M) = seqmx_of_mx (usubmx M).
Proof.
move=> M ; apply/seqmxP ; split=> [|i Hi|i j].
  + rewrite size_take !size_seqmx; case:m2=> [|p] ; first by rewrite addn0 ltnn.
    by rewrite addnS leq_addr.
  + by rewrite /rowseqmx nth_take // size_row_seqmx //; exact:ltn_addr.
  by rewrite /fun_of_seqmx /rowseqmx nth_take // mxE -seqmxE.
Qed.

Lemma dsubseqmxE : forall (M:'M[mT]_(m1+m2,n)),
  dsubseqmx (seqmx_of_mx M) = seqmx_of_mx (dsubmx M).
Proof.
move=> M ; apply/seqmxP ; split=> [|i Hi|i j].
  + by rewrite size_drop !size_seqmx addKn.
  + by rewrite /rowseqmx nth_drop // size_row_seqmx // ltn_add2l.
  by rewrite /fun_of_seqmx /rowseqmx nth_drop // mxE -seqmxE.
Qed.

Lemma lsubseqmxE : forall (M:'M[mT]_(m,n1+n2)),
  lsubseqmx (seqmx_of_mx M) = seqmx_of_mx (lsubmx M).
Proof.
move=> M ; apply/seqmxP ; split=> [|i Hi|i j].
  + by rewrite size_map size_seqmx.
  + rewrite /rowseqmx (nth_map [::]) ?size_seqmx // size_take size_row_seqmx //.
    case:n2=> [|p] ; first by rewrite addn0 ltnn.
    by rewrite addnS leq_addr.
  + rewrite /fun_of_seqmx /rowseqmx (nth_map [::]) ?size_seqmx //.
  by rewrite nth_take // mxE -seqmxE.
Qed.

Lemma rsubseqmxE : forall (M:'M[mT]_(m,n1+n2)),
  rsubseqmx (seqmx_of_mx M) = seqmx_of_mx (rsubmx M).
Proof.
move=> M ; apply/seqmxP ; split=> [|i Hi|i j].
  + by rewrite size_map size_seqmx.
  + rewrite /rowseqmx (nth_map [::]) ?size_seqmx // size_drop.
    by rewrite size_row_seqmx // addKn.
  + rewrite /fun_of_seqmx /rowseqmx (nth_map [::]) ?size_seqmx //.
  by rewrite nth_drop // mxE -seqmxE.
Qed.

End SeqmxRowCol.

Section SeqmxRowCol2.

Variables m m1 m2 n n1 n2 : nat.

Definition ulsubseqmx (M : seqmatrix) :=
  map (take n1) (take m1 M).

Definition ursubseqmx (M : seqmatrix) :=
  map (drop n1) (take m1 M).

Definition dlsubseqmx (M : seqmatrix) :=
  map (take n1) (drop m1 M).

Definition drsubseqmx (M : seqmatrix) :=
  map (drop n1) (drop m1 M).

Lemma ulsubseqmxE (M:'M[mT]_(m1+m2,n1+n2)) :
  ulsubseqmx (seqmx_of_mx M) = seqmx_of_mx (ulsubmx M).
Proof. by rewrite -lsubseqmxE -usubseqmxE. Qed.

Lemma ursubseqmxE (M:'M[mT]_(m1+m2,n1+n2)) :
  ursubseqmx (seqmx_of_mx M) = seqmx_of_mx (ursubmx M).
Proof. by rewrite -rsubseqmxE -usubseqmxE. Qed.

Lemma dlsubseqmxE (M:'M[mT]_(m1+m2,n1+n2)) :
  dlsubseqmx (seqmx_of_mx M) = seqmx_of_mx (dlsubmx M).
Proof. by rewrite -lsubseqmxE -dsubseqmxE. Qed.

Lemma drsubseqmxE (M:'M[mT]_(m1+m2,n1+n2)) :
  drsubseqmx (seqmx_of_mx M) = seqmx_of_mx (drsubmx M).
Proof. by rewrite -rsubseqmxE -dsubseqmxE. Qed.

Definition row_seqmx (M N : seqmatrix) : seqmatrix :=
  zipwith cat M N.

Definition col_seqmx (M N : seqmatrix) : seqmatrix :=
  M ++ N.

Definition block_seqmx Aul Aur Adl Adr : seqmatrix :=
  col_seqmx (row_seqmx Aul Aur) (row_seqmx Adl Adr).

Lemma size_row_row_seqmx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) i :
  i < m -> size (rowseqmx (row_seqmx (seqmx_of_mx A1) (seqmx_of_mx A2)) i) = (n1 + n2)%N.
Proof.
move=> Hi; rewrite /rowseqmx /row_seqmx (nth_zipwith _ [::] [::]).
  by rewrite size_cat !size_row_seqmx.
by rewrite !size_seqmx minnn.
Qed.

Lemma row_seqmxE (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row_seqmx (seqmx_of_mx A1) (seqmx_of_mx A2) = seqmx_of_mx (row_mx A1 A2).
Proof.
apply/seqmxP; split=>[|i Hi|i j].
+ by rewrite size_zipwith !size_seqmx minnn.
+ by rewrite size_row_row_seqmx.
+ rewrite mxE /fun_of_seqmx /rowseqmx !(nth_zipwith _ [::] [::]) ?size_seqmx.
  rewrite nth_cat size_row_seqmx //.
  by case:(splitP j)=> j' ->; rewrite ?addKn -seqmxE.
by rewrite minnn.
Qed.

Lemma size_row_col_seqmx (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) i :
  i < m1 + m2 -> size (rowseqmx (col_seqmx (seqmx_of_mx A1) (seqmx_of_mx A2)) i) = n.
Proof.
move=> Hi; rewrite /col_seqmx /rowseqmx nth_cat !size_seqmx.
case H:(i < m1); first by rewrite size_row_seqmx.
rewrite size_row_seqmx // -(ltn_add2r m1) subnK; first by rewrite addnC.
by rewrite leqNgt H.
Qed.

Lemma col_seqmxE (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col_seqmx (seqmx_of_mx A1) (seqmx_of_mx A2) = seqmx_of_mx (col_mx A1 A2).
Proof.
apply/seqmxP; split=>[|i Hi|i j].
  by rewrite size_cat !size_seqmx.
 by rewrite size_row_col_seqmx.
 rewrite mxE /fun_of_seqmx /rowseqmx.
rewrite nth_cat size_seqmx.
by case:(splitP i)=> i' ->; rewrite ?addKn -seqmxE.
Qed.

End SeqmxRowCol2.

(*
Definition comp_row_add_block iM iN dx (M N:comp_row) :=
  init dx (fun k => get M (iM+k) + get N (iN+k)) default.

Definition comp_matrix_add_block (xM xN:int*int) (dx dy:int) (M N:comp_matrix) :=
  init dy (fun k => comp_row_add_block xM.1 xN.1 dx (get M (xM.2+k)) (get N (xN.2+k))) (make 0 default) : comp_matrix.

Definition comp_row_sub_block iM iN dx (M N:comp_row) :=
  init dx (fun k => get M (iM+k) - get N (iN+k)) default.

Definition comp_matrix_sub_block (xM xN:int*int) (dx dy:int) (M N:comp_matrix) :=
  init dy (fun k => comp_row_sub_block xM.1 xN.1 dx (get M (xM.2+k)) (get N (xN.2+k))) (make 0 default) : comp_matrix.

Definition comp_matrix_opE := (comp_matrix_addE, comp_matrix_mulE).
*)

Section SeqmxBlock.

Variables m1 m2 n1 n2 : nat.

Lemma block_seqmxE (Aul : 'M_(m1,n1)) (Aur:'M_(m1,n2)) (Adl:'M_(m2,n1)) (Adr:'M[mT]_(m2,n2)) :
  block_seqmx (seqmx_of_mx Aul) (seqmx_of_mx Aur)
  (seqmx_of_mx Adl) (seqmx_of_mx Adr) =
  seqmx_of_mx (block_mx Aul Aur Adl Adr).
Proof. by rewrite /block_seqmx !row_seqmxE col_seqmxE. Qed.

Lemma cast_seqmx (M:'M[mT]_(m1,n1)) (H1 : m1=m2) (H2 : n1=n2) :
  seqmx_of_mx (castmx (H1,H2) M) = seqmx_of_mx M.
Proof.
apply/seqmxP; split=> [|i Hi| i j] ; first by rewrite size_seqmx.
  by rewrite size_row_seqmx ?H2 // -H1.
rewrite -seqmxE ; congr fun_of_seqmx ; move: (H1) (H2) M ; rewrite H1 H2=> H3 H4 M.
by rewrite castmx_id.
Qed.

Definition xrowseqmx (M : seqmatrix) : seqmatrix :=
  let R := set_nth [::] M m1 (nth [::] M m2) in
  set_nth [::] R m2 (nth [::] M m1).

End SeqmxBlock.

Definition scalar_seqmx (n : nat) (x : mT) :=
  mkseqmx n n (fun i j => x *+ (i == j)).

Lemma scalar_seqmxE n x :
  scalar_seqmx n x = seqmx_of_mx (@scalar_mx mT n x).
Proof.
apply/seqmxP ; split=> [||i j] ; first by rewrite size_map size_iota.
  exact:size_row_mkseqmx.
by rewrite mkseqmxE // mxE.
Qed.

Definition scaleseqmx (x : mT) (M : seqmatrix) :=
  map (map ( *%R x)) M.

Lemma scaleseqmxE m n x (M : 'M_(m,n)) :
  scaleseqmx x (seqmx_of_mx M) = seqmx_of_mx (scalemx x M).
Proof.
apply/seqmxP; split=> [|i Hi| i j] ; first by rewrite size_map size_seqmx.
  by rewrite /rowseqmx (nth_map [::]) ?size_seqmx // size_map size_row_seqmx.
rewrite mxE /fun_of_seqmx /rowseqmx (nth_map [::]) ?size_seqmx // (nth_map 0).
  by rewrite -seqmxE.
by rewrite size_row_seqmx.
Qed.

End seqmx.
