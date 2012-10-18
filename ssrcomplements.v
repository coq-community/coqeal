(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype finfun perm matrix bigop zmodp mxalgebra.
Require Import choice poly polydiv polyorder mxpoly binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

(** This file contains definitions and lemmas that are generic enough that
we could try to integrate them in Math Components' library.
Definitions and theories are gathered according to the file of the
library which they could be moved to. *)

(********************* seq.v *********************)
Section Seq.

Section seq_Type.

Variables (T1 T2 T3 : Type) (f : T1 -> T2 -> T3).

Fixpoint zipwith (s1 : seq T1) (s2 : seq T2) :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then f x1 x2 :: zipwith s1' s2' else [::]
  else [::].

Lemma size_zipwith s1 s2 :
  size (zipwith s1 s2) = minn (size s1) (size s2).
Proof.
elim:s1 s2=>[s2|t1 s1 IHs] ; first by rewrite min0n.
by case=>[|t2 s2] //= ; rewrite IHs /minn /leq subSS ; case:ifP.
Qed.

Lemma nth_zipwith x1 x2 x3 n s1 s2 :
  n < minn (size s1) (size s2) ->
  nth x3 (zipwith s1 s2) n = f (nth x1 s1 n) (nth x2 s2 n).
Proof.
elim:s1 n s2=> [n s2|t1 s1 IHs]; first by rewrite min0n ltn0.
case=>[|n]; first by case.
by case=> // t2 s2 H ; rewrite /= IHs // ; move:H ; rewrite !leq_min.
Qed.

Fixpoint foldl2 (f : T3 -> T1 -> T2 -> T3) z (s : seq T1) (t : seq T2) {struct s} :=
  if s is x :: s' then
    if t is y :: t' then foldl2 f (f z x y) s' t' else z
  else z.

Lemma seq2_ind (P : seq T1 -> seq T2 -> Prop) : P [::] [::] ->
 (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
  forall s1 s2, size s1 = size s2 -> P s1 s2.
Proof.
move=> HP IHP.
elim=> [|x1 l1 IH1]; case=> // x2 l2 /= Hs.
apply: IHP; apply: IH1.
by move/eqnP: Hs=> /= /eqnP.
Qed.

Lemma rcons_nseq k (x : T1) : rcons (nseq k x) x = nseq k.+1 x.
Proof. by elim: k=> // n /= ->. Qed.

Lemma nseq_cat m n (x : T1) : nseq m x ++ nseq n x = nseq (m + n) x.
Proof. by elim: m=> // m /= ->. Qed.

Lemma count_rcons P (a : T1) (l : seq T1) :
  count P (rcons l a) = (P a + count P l)%N.
Proof. by elim: l=> //= b l ->; rewrite addnA (addnC (P b)) addnA. Qed.

Lemma count_nseq P n (a : T1) : count P (nseq n a) = (n * (P a))%N.
Proof. by elim: n=> //= n ->; rewrite mulSn. Qed.

Lemma nth_dflt_take x0 (s : seq T1) n :
  forall i, n <= i -> nth x0 (take n s) i = x0.
Proof.
move=> i Hi.
rewrite nth_default // size_take; case: ifP=> // /negbT.
by rewrite -leqNgt=> H; apply: leq_trans Hi.
Qed.

Lemma flatten_map (g : T1 -> T2) (s : seq (seq T1)) :
  map g (flatten s) = flatten (map (map g) s).
Proof.
by elim: s=> // a l IHl /=; rewrite map_cat IHl.
Qed.

Lemma size_filter (s : seq T1) P : size (filter P s) <= size s.
Proof.
by elim: s=> //= a l IHl; case: (P a)=> //=; apply: (leq_trans IHl).
Qed.

End seq_Type.

Section seq_eqType.

Variable T1 T2 : eqType.

Lemma undup_nil (s : seq T1) : (undup s == [::]) = (s == [::]).
Proof.
elim: s=> // a l /=.
case: ifP=> // Ha ->.
by case: l Ha.
Qed.

Lemma mem_flatten (l : seq T1) (ss : seq (seq T1)) x :
  x \in l -> l \in ss -> x \in (flatten ss).
Proof.
elim: ss=> // a s IH Hxl.
rewrite in_cons=> Hls /=.
rewrite mem_cat; apply/orP.
case/orP: Hls=> [/eqP <-| Hl]; [left|right]=> //.
exact: IH.
Qed.

Lemma mem_flattenP (ss : seq (seq T1)) x :
  reflect (exists2 s, x \in s & s \in ss) (x \in (flatten ss)).
Proof.
apply: (iffP idP)=> [H|].
  pose g := (fix loop  (ll : seq (seq T1)) x :=
    if ll is l :: tll then (if (x \in l) then l else (loop tll x))
    else [::]).
  exists (g ss x); elim: ss H=>// aa ll IH /=; rewrite mem_cat; case/orP=>[H|H].
    +by rewrite H.
    -by case: ifP=> H2 //; apply: IH.
    +by rewrite H mem_head.
  case: ifP=> _; first by rewrite mem_head.
  by rewrite mem_behead //; apply: (IH H).
case=> l Hl1 Hl2.
exact: (mem_flatten Hl1).
Qed.

Lemma mem_nseq i n (a : T1) : i \in nseq n a -> i = a.
Proof.
by elim: n=> // n IHn; rewrite /= in_cons; case/orP=> // /eqP.
Qed.

Lemma map_perm_eq (g : T1 -> T2) s1 s2 : injective g ->
  perm_eq (map g s1) (map g s2) -> perm_eq s1 s2.
Proof.
move=> Hg; rewrite /perm_eq /same_count1=> /allP H.
apply/allP=> x Hx.
have:= (H (g x)).
rewrite -map_cat (mem_map Hg)=> H2.
have:= (H2 Hx).
rewrite !count_map.
have Hp: preim g (pred1 (g x)) =1 pred1 x.
  by move=> y /=; apply: inj_eq.
by rewrite !(eq_count Hp).
Qed.

Lemma count_rem P (l : seq T1) x : x \in l ->
  count P (rem x l) = if P x then (count P l).-1 else count P l.
Proof.
elim: l=> // a l IHl Hx /=.
have Hxla: (a == x) = false -> x \in l.
  by move=> Hax; rewrite in_cons eq_sym Hax in Hx.
case HP: (P x); case Hax: (a == x)=> /=.
  +by rewrite (eqP Hax) HP.
  -have Hxl := Hxla Hax.
   rewrite IHl // HP -{2}(@prednK (count P _)) ?addnS // -has_count.
   by apply/hasP; exists x.
  +by rewrite (eqP Hax) HP.
  -have Hxl := Hxla Hax.
   by rewrite IHl // HP.
Qed.

Lemma count_perm_eq (s1 s2 : seq T1) :
  size s1 = size s2 ->
  (forall x, x \in s1 -> count (xpred1 x) s1 = count (xpred1 x) s2) ->
  perm_eq s1 s2.
Proof.
elim: s1 s2 =>[|a1 l1 IHl1]; case=> // a2 l2 Hs H.
have Ha1: a1 \in a2 :: l2.
  by rewrite -has_pred1 has_count -H ?mem_head //= eqxx.
rewrite perm_eq_sym.
apply:  (perm_eq_trans (perm_to_rem Ha1)).
rewrite perm_cons perm_eq_sym.
apply: IHl1; first by rewrite size_rem // -Hs.
move=> x Hx.
have ->: l1 = rem a1 (a1 :: l1) by rewrite /= eqxx.
rewrite !count_rem // ?mem_head //.
by rewrite H // mem_behead.
Qed.

(*****  Lemma about sorted ****************)

Lemma sorted_trans (leT1 leT2 : rel T1) s :
  {in s &, (forall x y, leT1 x y -> leT2 x y)} ->
  sorted leT1 s -> sorted leT2 s.
Proof.
elim: s=> // a [] //= b l IHl HleT /andP [H1 H2].
apply/andP; split.
apply: HleT=> //.
    exact: mem_head.
  by rewrite mem_behead // mem_head.
apply: IHl=> // x y Hx Hy.
by apply/HleT; apply: mem_behead.
Qed.

Lemma sorted_take (leT : rel T1) (s :seq T1) n :
  sorted leT s -> sorted leT (take n s).
Proof.
case: (ltnP n (size s))=> [|H]; last by rewrite take_oversize.
elim: s n=> // a l IHl [] // n.
rewrite /= ltnS.
case: l IHl n=> // b l IHl [] // n Hn /andP [H1 H2].
apply/andP; split=> //.
exact: (IHl n.+1).
Qed.

Lemma sorted_nth (leT : rel T1) x0 (s :seq T1) :
  reflexive leT -> transitive leT ->
  sorted leT s -> forall i j, j < size s -> i <= j ->
  leT (nth x0 s i) (nth x0 s j).
Proof.
move=> Hr Ht; elim: s => [_ i j H _| a l IHl Hs i j] //.
case: j; first by rewrite leqn0=> _ /eqP ->; apply: Hr.
move=> j; case: i => [Hj _|i Hj Hij].
  have/allP H: all (leT a) l by apply: order_path_min=> //; apply: Ht.
  by rewrite nth0 -nth_behead; apply: H; rewrite mem_nth.
have IHsl: sorted leT l by apply: (@path_sorted _ _ a).
have IHj: j < size l by [].
have IHij: i <= j by [].
by rewrite -!nth_behead; apply: IHl.
Qed.

Lemma sorted_nthr (leT : rel T1) x0 (s :seq T1) :
  reflexive leT -> transitive leT -> {in s, (forall x, leT x x0)} ->
  sorted leT s -> forall i j, i <= j -> leT (nth x0 s i) (nth x0 s j).
Proof.
move=> Hr Ht Hx0 Hs i j.
case: (ltnP j  (size s))=> [|Hij]; first exact: sorted_nth.
case: (ltnP i (size s))=> Hi.
  by rewrite (@nth_default _ _ _ j) // => _; apply/Hx0/mem_nth.
by rewrite !nth_default.
Qed.

Lemma sorted_map (leT1 : rel T1) (leT2 : rel T2)
  (g : T1 -> T2) s :
  {in s &, (forall x y, leT1 x y -> leT2 (g x) (g y))} -> sorted leT1 s ->
  sorted leT2 (map g s).
Proof.
elim: s=> // a.
case=> // b l /= IHl HleT /andP [H1 H2].
apply/andP; split.
apply: HleT=> //.
    exact: mem_head.
  by rewrite mem_behead // mem_head.
apply: IHl=> // x y Hx Hy.
by apply: HleT; apply: mem_behead.
Qed.

End seq_eqType.

Section seq_comRingType.

Local Open Scope ring_scope.
Import GRing.Theory.
Variable R : comRingType.
Variable T : eqType.

Lemma prod_seq_count (s : seq T) (F : T -> R) :
  \prod_(i <- s) F i =
  \prod_(i <- (undup s)) ((F i) ^+ (count (xpred1 i) s)).
Proof.
elim: s=> /= [|a l IHl]; first by rewrite !big_nil.
rewrite big_cons IHl.
set r:= if _ then _ else _.
have ->: \big[*%R/1]_(i <- r) (F i) ^+ ((a == i) + count (eq_op^~ i) l) =
         \big[*%R/1]_(i <- r) (F i) ^+ (a == i) *
         \big[*%R/1]_(i <- r) (F i) ^+ (count (eq_op^~ i) l).
  by rewrite -big_split /=; apply: eq_bigr=> i _; rewrite exprD.
have ->: \big[*%R/1]_(i <- r) (F i) ^+ (a == i) = F a.
  rewrite /r; case Hal: (a \in l).
    have Ha: a \in undup l by rewrite mem_undup.
    rewrite (bigD1_seq _ Ha (undup_uniq l)) /= eqxx big1 ?mulr1 //.
    by move=> i /negbTE Hai; rewrite eq_sym Hai.
  rewrite big_cons eqxx big1_seq ?mulr1 // => i /= Hi.
  case Hai: (a == i)=> //.
  by rewrite (eqP Hai) -mem_undup Hi in Hal.
rewrite /r; case H: (a \in l)=> //.
rewrite big_cons.
have->: count (xpred1 a) l = 0%N.
  by apply/eqP; rewrite -leqn0 leqNgt -has_count has_pred1 H.
by rewrite mul1r.
Qed.

End seq_comRingType.

End Seq.

Section FinType.

Lemma enum_ord_enum n : enum 'I_n = ord_enum n.
Proof. by rewrite enumT unlock. Qed.

End FinType.


Section Finfun.

Variables (aT : finType) (rT : eqType).
Variables (f g : aT -> rT).
Variable (P : pred aT).
Hypothesis (Hf : injective f) (Hg : injective g).

Lemma uniq_image (h : aT -> rT):
  injective h -> uniq (image h P).
Proof. by move/map_inj_uniq=> ->; rewrite enum_uniq. Qed.
 
Lemma perm_eq_image :  {subset (image f P) <= (image g P)} ->
  perm_eq (image f P) (image g P).
Proof.
move=> Hsub.
rewrite uniq_perm_eq // ?uniq_image //.
have []:= (leq_size_perm (uniq_image Hf) Hsub)=> //.
by rewrite !size_map.
Qed.

End Finfun.

Section BigOp.

Variables (T : Type) (idx : T) (op : T -> T -> T).
Variables (opm : Monoid.law idx) (opc : Monoid.com_law idx).

Lemma sumn_big s : sumn s = (\sum_(i <- s) i)%N.
Proof.
elim: s=> /= [|a l ->]; first by rewrite big_nil.
by rewrite big_cons.
Qed.

Lemma big_lift_ord n F j :
  \big[opc/idx]_( i < n.+1 | j != i ) F i = \big[opc/idx]_i F (lift j i).
Proof.
case: (pickP 'I_n) => [k0 _ | n0]; last first.
  by rewrite !big1 // => [k /unlift_some[i] | i _]; have:= n0 i.
rewrite (reindex (lift j)).
  by apply: eq_bigl=> k; rewrite neq_lift.
exists (fun k => odflt k0 (unlift j k)) => k; first by rewrite liftK.
by case/unlift_some=> k' -> ->.
Qed.

End BigOp.

(********************* matrix.v *********************)
Notation castmx_nn eqn := (castmx (eqn,eqn)).

Section Matrix.

Local Open Scope ring_scope.
Import GRing.Theory.

Section matrix_Type.

Variable T : Type.

(* It is a definition for castmx on square matrices *)
Definition pairxx (x : T) := pair x x.

Lemma matrix_comp k l m n (E : 'I_k -> 'I_l -> T) (F : 'I_n -> 'I_k) G :  
  \matrix_(i < n, j < m) ((\matrix_(i0 < k, j0 < l) E i0 j0) (F i) (G j)) =
  \matrix_(i, j) (E (F i) (G j)).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col_matrixP (m n : nat) :
  forall (A B : 'M[T]_(m,n)), (forall i, col i A = col i B) <-> A = B.
Proof.
split=> [eqAB | -> //]; apply/matrixP=> i j.
by move/colP/(_ i): (eqAB j); rewrite !mxE.
Qed.

Lemma row'_col'C n m (i : 'I_n) (j : 'I_m) (A : 'M[T]_(n,m)) :
  row' i (col' j A) = col' j (row' i A).
Proof. by apply/matrixP=> k l; rewrite !mxE. Qed.

Lemma row_thin_mx  p q (M : 'M_(p,0)) (N : 'M[T]_(p,q)) :
  row_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP=> [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

Lemma col_flat_mx p q (M : 'M[T]_(0, q)) (N : 'M_(p,q)) :
  col_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP => [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

Lemma block_flat_mx m n (M : 'M[T]_(0,m)) (N : 'M_(n, 0)) (P : 'M_(0,0))
  (Q : 'M_(n,m)) : block_mx P M N Q = Q.
Proof.
by rewrite /block_mx !row_thin_mx col_flat_mx.
Qed.

Lemma tr_mxvec m n (M : 'M[T]_(m,n)) i j :
  (mxvec M) 0 (mxvec_index i j) = (mxvec M^T) 0 (mxvec_index j i).
Proof. by rewrite !mxvecE mxE. Qed.

End matrix_Type.

Section matrix_zmodType.

Variable V : zmodType.

Lemma mxvec0 m n : mxvec (0 : 'M[V]_(m,n)) = 0 :> 'rV[V]_(m * n).
Proof. by apply/eqP; rewrite mxvec_eq0. Qed.

End matrix_zmodType.

Section matrix_ringType.

Variable R : ringType.

(* Lemmas about column operations *)
Lemma colE (m n : nat) i (A : 'M[R]_(m, n)) : col i A = A *m delta_mx i 0.
Proof.
apply/colP=> j; rewrite !mxE (bigD1 i) //= mxE !eqxx mulr1.
by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mulr0.
Qed.

Lemma col_mul m n p (i : 'I_p) (A : 'M[R]_(m,n)) (B : 'M[R]_(n, p)) :
  col i (A *m B) = A *m col i B.
Proof. by rewrite !colE mulmxA. Qed.

Lemma col_id_mulmx m n (M : 'M[R]_(m,n)) i :
  M *m col i 1%:M = col i M.
Proof.
apply/matrixP=> k l; rewrite !mxE.
rewrite (bigD1 i) // big1 /= ?addr0 ?mxE ?eqxx ?mulr1 // => j /negbTE Hj.
by rewrite !mxE Hj mulr0.
Qed.

Lemma row_id_mulmx m n (M : 'M[R]_(m,n)) i :
   row i 1%:M *m M = row i M.
Proof.
apply/matrixP=> k l; rewrite !mxE.
rewrite (bigD1 i) // big1 /= ?addr0 ?mxE ?eqxx ?mul1r // => j /negbTE Hj.
by rewrite !mxE eq_sym Hj mul0r.
Qed.

Lemma row'_col'_char_poly_mx m i (M : 'M[R]_m) :
  row' i (col' i (char_poly_mx M)) = char_poly_mx (row' i (col' i M)).
Proof.
apply/matrixP=> k l; rewrite !mxE.
suff ->: (lift i k == lift i l) = (k == l) => //.
by apply/inj_eq/lift_inj.
Qed.

(*vrai aussi pour A B C D (modulo map_mx polyC)*)
Lemma char_block_mx m n (A : 'M[R]_m) (B : 'M[R]_n) :
  char_poly_mx (block_mx A 0 0 B) =
  block_mx (char_poly_mx A) 0 0 (char_poly_mx B).
Proof.
apply/matrixP=> i j; rewrite !mxE.
case: splitP=> k Hk; rewrite !mxE; case: splitP=> l Hl; rewrite !mxE;
rewrite -!(inj_eq (@ord_inj _)) Hk Hl ?subr0 ?eqn_add2l //.
  by rewrite ltn_eqF // ltn_addr. 
by rewrite gtn_eqF // ltn_addr.
Qed.

(* Lemma about mxvec *)
Lemma scale_mxvec m n x (M : 'M[R]_(m,n)) : mxvec (x *: M) = x *: mxvec M.
Proof.
apply/rowP => i; rewrite mxE.
case/mxvec_indexP: i => i j.
by rewrite !mxvecE !mxE.
Qed.

(*about delta_mx*)
Lemma delta_mul_delta k n (A : 'M[R]_n) (i : 'I_k) (j : 'I_n) :
  delta_mx i j *m A *m delta_mx j i = (A j j) *: delta_mx i i.
Proof.
apply/matrixP=> l m; rewrite !mxE (bigD1 j) //= big1 ?addr0=>[|p].
  rewrite !mxE (bigD1 j) //= mxE big1 ?addr0=> [|p].
    rewrite !eqxx; case: (l == i); first by rewrite mul1r.
    by rewrite !mul0r mulr0.
  by rewrite mxE=> /negbTE ->; rewrite andbF mul0r.
by rewrite !mxE => /negbTE ->; rewrite mulr0.
Qed.

(* Lemma about detrminant *)

(* there are two proof of equality to not use the irrelevance *)
Lemma det_castmx n m(M : 'M[R]_n) (eq1 : n = m) (eq2 : n = m) :
  \det (castmx (eq1,eq2) M) = \det M.
Proof. by case: m / eq1 eq2=> eq2; rewrite castmx_id. Qed.


Lemma exp_block_mx m n (A: 'M[R]_m.+1) (B : 'M_n.+1) k :
  (block_mx A 0 0 B) ^+ k = block_mx (A ^+ k) 0 0 (B ^+ k).
Proof.
elim: k=> [|k IHk].
  by rewrite !expr0 -scalar_mx_block.
rewrite !exprS IHk /GRing.mul /= (mulmx_block A 0 0 B (A ^+ k)).
by rewrite !mulmx0 !mul0mx !add0r !addr0.
Qed.

Lemma char_castmx m n(A : 'M[R]_n) (eq : n = m) :
 castmx_nn eq (char_poly_mx A) = char_poly_mx (castmx_nn eq A).
Proof.
by case: m / eq; rewrite !castmx_id.
Qed.

End matrix_ringType.

Section matrix_comUnitRingType.

Variable R : comUnitRingType.

Lemma invmx_block n1 n2  (Aul : 'M[R]_n1.+1) (Adr : 'M[R]_n2.+1) :
   (block_mx Aul 0 0 Adr) \in unitmx ->
  (block_mx Aul 0 0 Adr)^-1 = block_mx Aul^-1 0 0 Adr^-1.
Proof.
move=> Hu.
have Hu2: (block_mx Aul 0 0 Adr) \is a GRing.unit by [].
rewrite unitmxE det_ublock unitrM in Hu.
case/andP: Hu; rewrite -!unitmxE => HAul HAur.
have H: block_mx Aul 0 0 Adr *  block_mx Aul^-1 0 0 Adr^-1 = 1.
  rewrite /GRing.mul /= (mulmx_block Aul _ _ _ Aul^-1) !mulmxV //.
  by rewrite !mul0mx !mulmx0 !add0r addr0 -scalar_mx_block.
by apply: (mulrI Hu2); rewrite H mulrV.
Qed.

End matrix_comUnitRingType.

Section matrix_fieldType.

Variable F : fieldType.

(* mx_poly *)
Lemma horner_mx_dvdp n (p q : {poly F}) (A : 'M_n.+1) :
  (dvdp p q) -> horner_mx A p = 0 -> horner_mx A q = 0.
Proof.
by case/dvdpP=> r ->; rewrite rmorphM=> /= ->; rewrite mulr0.
Qed.

Lemma mxminpolyP n (A : 'M[F]_n.+1) (p : {poly F}) :
  p \is monic -> horner_mx A p = 0 ->
  (forall q, horner_mx A q = 0 -> (dvdp p q)) ->
  p = mxminpoly A.
Proof.
move=> Hmp Hp0 Hpq.
apply/eqP; rewrite -eqp_monic //; last exact: mxminpoly_monic.
apply/andP; split.
  by apply: Hpq; apply: mx_root_minpoly.
exact: mxminpoly_min.
Qed.

End matrix_fieldType.

End Matrix.

(* Lemmas borrowed from mxtens *)
Section mxtens.

(* Cyril's lemma about cast of row_mx from mxtens *)
Lemma castmx_row (R : Type) (m m' n1 n2 n1' n2' : nat)
  (eq_n1 : n1 = n1') (eq_n2 : n2 = n2') (eq_n12 : (n1 + n2 = n1' + n2')%N)
  (eq_m : m = m') (A1 : 'M[R]_(m, n1)) (A2 : 'M_(m, n2)) :
  castmx (eq_m, eq_n12) (row_mx A1 A2) =
  row_mx (castmx (eq_m, eq_n1) A1) (castmx (eq_m, eq_n2) A2).
Proof.
case: _ / eq_n1 in eq_n12 *; case: _ / eq_n2 in eq_n12 *.
by case: _ / eq_m; rewrite castmx_id.
Qed.

(* We also use the lemma castmx_block, it is another lemma of section
ExtraMx of file mxtens. *)

End mxtens.

Section Polynomial.

Section binomial_poly.

Variable R : comRingType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma Newton (x : R) n :
  ('X + x%:P)^+n = \poly_(i < n.+1) ((x^+ (n - i)) *+ 'C(n,i)).
Proof.
rewrite poly_def addrC exprDn.
apply: eq_big=> // i _.
by rewrite -scalerMnl -mul_polyC rmorphX.
Qed.

Lemma Newton_XsubC (x : R) n :
  ('X - x%:P)^+n = \poly_(i < n.+1) (((-x)^+ (n - i)) *+ 'C(n,i)).
Proof. by rewrite -polyC_opp Newton. Qed.

Lemma Newton_coef (x : R) n i : (('X + x%:P)^+n)`_i = (x^+ (n - i)) *+ 'C(n,i).
Proof.
rewrite Newton coef_poly.
case H: (i < n.+1)=> //.
rewrite bin_small; first by rewrite mulr0n.
by rewrite ltnNge negbT.
Qed.

Lemma Newton_coef_XsubC (x : R) n i : 
 (('X - x%:P)^+n)`_i = ((-x)^+ (n - i)) *+ 'C(n,i).
Proof. by rewrite -polyC_opp Newton_coef. Qed.

End binomial_poly.

Section poly_ringType.

Open Scope ring_scope.
Variable R : ringType.

Lemma monic_size_1 (p : {poly R}) : p \is monic -> size p <= 1 -> p = 1.
Proof. 
move/monicP=> H Hp; rewrite [p]size1_polyC //.
have <- : (size p).-1 = 0%N by apply/eqP; rewrite -subn1 subn_eq0.
by rewrite -lead_coefE H.
Qed.

End poly_ringType.

Section poly_idomainType. 

Variable R : idomainType.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma size_prod_pos (s : seq {poly R}) : (forall p, p \in s -> 0 < size p) ->
  0 < size (\prod_(x <- s) x)%R.
Proof.
elim: s=> [|a l IHl Hp]; first by rewrite big_nil size_poly1.
have IHp : forall p, p \in l -> 0 < size p.
  by move=> p Hp1; apply: Hp; rewrite mem_behead.
have Ha: 0 < size a by apply: Hp; rewrite mem_head.
rewrite big_cons size_proper_mul.
  by rewrite -(prednK (IHl IHp)) addnS ltn_addr.
rewrite mulf_eq0 !lead_coef_eq0 -!size_poly_leq0.
by rewrite leqNgt Ha leqNgt IHl.
Qed.

Lemma coprimep_factor (a b : R) : (b - a)%R \is a GRing.unit ->
   coprimep ('X - a%:P) ('X - b%:P).
Proof.
move=> Hab; apply/Bezout_coprimepP.
exists ((b - a)^-1%:P , -(b - a) ^-1%:P).
rewrite /= !mulrBr !mulNr opprK -!addrA (addrC (- _)) !addrA addrN.
by rewrite add0r -mulrBr -rmorphB -rmorphM mulVr // eqpxx.
Qed.

Lemma coprimepn : forall n (sP_ : 'I_n -> {poly R}),
  (forall i j, i != j -> coprimep (sP_ i) (sP_ j)) <->
  (forall i, coprimep (sP_ i) (\prod_(j | i != j) sP_ j)).
Proof.
move=> n sP_; split=> H i.
  apply: (big_ind (coprimep (sP_ i))).
  -by apply: coprimep1.
  -by move=> x y Hcx Hcy; rewrite coprimep_mulr; apply/andP.
  -by apply: H.
by move=> j Hij; move: (H i); rewrite (bigD1 j) // coprimep_mulr; case/andP.
Qed.

Lemma lead_coef_prod (s : seq {poly R}) :
  \prod_(p <- s) lead_coef p = lead_coef (\prod_(p <- s) p).
Proof.
elim: s=> [|a l IHl]; first by rewrite !big_nil lead_coef1.
by rewrite !big_cons lead_coefM -IHl.
Qed.

Lemma lead_coef_scale (a : R) p : lead_coef (a *: p) = a * lead_coef p.
Proof.
by rewrite -mul_polyC lead_coefM lead_coefC.
Qed.

Lemma monic_leadVMp (p : {poly R}) : (lead_coef p) \is a GRing.unit ->
  ((lead_coef p)^-1 *: p) \is monic.
Proof.
by move=> H; apply/monicP; rewrite lead_coef_scale mulVr.
Qed.

Lemma lead_eq_eqp (p q : {poly R}) : (lead_coef p) \is a GRing.unit ->
 lead_coef p = lead_coef q ->  reflect (p = q) (p %= q).
Proof.
move=> H1 Hl; apply: (iffP idP).
  by move/eqp_eq; rewrite -Hl => /scaler_injl ->.
by move=> ->; rewrite eqpxx.
Qed.

Lemma coprimep_irreducible (p q : {poly R}) : ~~(p %= q) ->
  irreducible_poly p -> irreducible_poly q -> coprimep p q.
Proof.
move=> H [Hsp Hp] [Hsq Hq].
have Hdl:= (dvdp_gcdl p q).
have Hdr:= (dvdp_gcdr p q).
case: (altP (size (gcdp p q) =P 1%N))=> [/eqP|Hb] //.
have:= (Hp _ Hb Hdl); rewrite eqp_sym /eqp dvdp_gcd.
case/andP=> [/andP [ _ Hpq]] _.
have:= (Hq _ Hb Hdr); rewrite eqp_sym /eqp dvdp_gcd.
case/andP=> [/andP [Hqp _]] _.
by move: H; rewrite /eqp Hpq Hqp.
Qed.

Lemma irreducible_dvdp_seq (p r : {poly R}) s :
    irreducible_poly p -> p \is monic -> (dvdp p r) ->
    (forall q, q \in s -> irreducible_poly q) ->
    (forall q, q \in s -> q \is monic) ->
    r = \prod_(t <- s) t ->
    p \in s.
Proof.
move=> HpIrr Hpm.
elim: s r => [r Hpr _ _|a l IHl r Hpr Hirr Hm].
  rewrite big_nil=> H; move: Hpr HpIrr.
  rewrite H dvdp1 /irreducible_poly=> /eqP ->.
  by rewrite ltnn; case.
rewrite big_cons=> Hr; move: Hpr; rewrite Hr=> Hd.
case Hpa: (eqp p a); move: Hpa.
  have Hma: a \is monic by apply: Hm; rewrite mem_head.
  by rewrite eqp_monic // => /eqP ->; rewrite mem_head.
have Hia: irreducible_poly a by apply: Hirr; rewrite mem_head.
move/negbT=> H.
have Hcpa := coprimep_irreducible H HpIrr Hia.
move: Hd; rewrite (Gauss_dvdpr _ Hcpa)=> Hd.
apply/mem_behead/(IHl _ Hd)=> // q Hq.
  by apply: Hirr; rewrite mem_behead.
by apply: Hm; rewrite mem_behead.
Qed.

Lemma unicity_decomposition (s1 s2 : seq {poly R}) : forall (p : {poly R}),
  (forall r, r \in s1 -> irreducible_poly r) ->
  (forall r, r \in s2 -> irreducible_poly r) ->
  (forall r, r \in s1 -> r \is monic) ->
  (forall r, r \in s2 -> r \is monic) ->
  p = \prod_(r <- s1) r ->  p = \prod_(r <- s2) r ->
  perm_eq s1 s2.
Proof.
elim: s1 s2=> [|a1 l1 IHl s2 p Hirr1 Hirr2 Hm1 Hm2].
  case=> // a l p _ Hirr2 _ Hm2->.
  rewrite big_nil big_cons=> H.
  have: irreducible_poly a by apply: Hirr2; rewrite mem_head.
  rewrite /irreducible_poly; case.
  by rewrite ltnNge leq_eqVlt -dvdp1 H dvdp_mulr.
rewrite big_cons=> Hp1 Hp2 /=.
have Ha1s2: a1 \in s2.
  apply: (irreducible_dvdp_seq _ _ _ Hirr2 Hm2 Hp2).
  +by apply: Hirr1; rewrite mem_head.
  -by apply: Hm1; rewrite mem_head.
  by rewrite Hp1 dvdp_mulr.
rewrite perm_eq_sym.
apply:  (perm_eq_trans (perm_to_rem Ha1s2)).
rewrite perm_cons perm_eq_sym.
have Ha1: a1 != 0.
  by apply: irredp_neq0; apply: Hirr1; rewrite mem_head.
move: Hp2; rewrite (eq_big_perm _ (perm_to_rem Ha1s2)) /= big_cons Hp1.
move/(mulfI Ha1)=> H.
set q:= \prod_(j <- l1) j.
apply: (IHl _ q)=> // [r Hr|r Hr|r Hr|r Hr].
  +by apply: Hirr1; rewrite mem_behead.
  -by apply: Hirr2; rewrite (mem_rem Hr).
  +by apply: Hm1; rewrite mem_behead.
  -by apply: Hm2; rewrite (mem_rem Hr).
Qed.

Lemma gcdpA (p q r : {poly R}):
 (gcdp p (gcdp q r) %= gcdp (gcdp p q) r).
Proof.
apply/andP; split; rewrite dvdp_gcd; apply/andP; split.
  +rewrite dvdp_gcd; apply/andP; split; first exact: dvdp_gcdl.
   exact: (dvdp_trans (dvdp_gcdr _ _) (dvdp_gcdl _ _)).
  +exact: (dvdp_trans (dvdp_gcdr _ _) (dvdp_gcdr _ _)).
  +exact: (dvdp_trans (dvdp_gcdl _ _) (dvdp_gcdl _ _)).
  +rewrite dvdp_gcd; apply/andP; split; last exact: dvdp_gcdr.
   exact: (dvdp_trans (dvdp_gcdl _ _) (dvdp_gcdr _ _)).
Qed.

End poly_idomainType.

Section poly_closedFieldType.

Variable F :  closedFieldType.
Import GRing.Theory.

Local Open Scope ring_scope.

Definition root_seq : {poly F} -> seq F :=
  let fix loop (p : {poly F}) (n : nat) :=
    if n is n.+1 then
      if (size p != 1%N) =P true is ReflectT p_neq0
        then let x := projT1 (sigW (closed_rootP p p_neq0)) in
          x :: loop (p %/ ('X - x%:P)) n
        else [::]
      else [::]
  in fun p => loop p (size p).

Lemma root_root_seq (p : {poly F}) x : p != 0 -> x \in root_seq p = root p x.
Proof.
rewrite /root_seq; set loop := fix loop p n := if n is _.+1 then _ else _.
elim: size {-2 5}p (erefl (size p))=> /= {p} [|n ihn] p /=.
  by move/eqP; rewrite size_poly_eq0=> /eqP->; rewrite eqxx.
case: eqP=> /= [sp_neq1 sp_eqn|/negP]; last first.
  rewrite negbK=> /size_poly1P [c c_neq0 ->] _ _.
  by rewrite rootC (negPf c_neq0).
case: sigW=> z /= rpz p_neq0.
rewrite in_cons; have [->|neq_xz] //= := altP eqP.
move: rpz sp_eqn => /factor_theorem [q ->].
rewrite mulpK ?polyXsubC_eq0 // rootM root_XsubC (negPf neq_xz) orbF.
have [->|q_neq0] := eqVneq q 0; first by rewrite mul0r size_poly0.
rewrite size_mul ?polyXsubC_eq0 // size_XsubC addn2.
by case=> /ihn /(_ q_neq0).
Qed.

Lemma root_seq_cons (p : {poly F}) x s : root_seq p = x :: s -> 
  s = root_seq (p %/ ('X - x%:P)).
Proof.
rewrite /root_seq; set loop := fix loop p n := if n is _.+1 then _ else _.
case H: (size p)=> [|n] //=; case: eqP=> // Hp.
move/eqP; rewrite eqseq_cons; case/andP=> /eqP {1}<- /eqP <-.
suff ->: n = size (p %/ ('X - x%:P))=> //. 
by rewrite size_divp ?polyXsubC_eq0 // size_XsubC subn1 H.
Qed.

Lemma root_seq_eq (p : {poly F}) : 
  p = lead_coef p *: \prod_(x <- root_seq p) ('X - x%:P).
Proof.
move: {2}(root_seq p) (erefl (root_seq p))=> s.
elim: s p=> [p | x s IHp p].
  rewrite /root_seq; set loop := fix loop p n := if n is _.+1 then _ else _.
  case H: (size p)=> [|n].
    move/eqP: H; rewrite size_poly_eq0=> /eqP ->.   
    by rewrite lead_coef0 scale0r.
  case: n H=> [H | n H] /=; case: eqP=> //.
    move=> _ _; rewrite big_nil.
    move/eqP: H => /size_poly1P [c H] ->.
    by rewrite lead_coefC alg_polyC.
  by move/negP; rewrite negbK H.
move=> H; rewrite H big_cons (root_seq_cons H) mulrC scalerAl.
have Hfp : p = p %/ ('X - x%:P) * ('X - x%:P).
  apply/eqP; rewrite -dvdp_eq dvdp_XsubCl -root_root_seq.
    by rewrite H mem_head.
  move: H; rewrite /root_seq.
  set loop := fix loop p n := if n is _.+1 then _ else _.
  case Hp: (p != 0)=> //.
  by move/negbT: Hp; rewrite negbK -size_poly_eq0 => /eqP ->.
suff -> : lead_coef p = lead_coef (p %/ ('X - x%:P)).
  by rewrite -IHp ?(root_seq_cons H).
by rewrite {1}Hfp lead_coef_Mmonic // monicXsubC.
Qed.

Lemma root_seq0 : root_seq 0 = [::].
Proof. by rewrite /root_seq size_poly0. Qed.

Lemma size_root_seq p : size (root_seq p) = (size p).-1.
Proof.  
case Hp: (p == 0).
  by rewrite (eqP Hp) root_seq0 size_poly0.
rewrite {2}[p]root_seq_eq size_scale ?lead_coef_eq0 ?Hp //.
rewrite (big_nth 0) big_mkord size_prod.
  rewrite (eq_bigr (fun i => (1 + 1)%N)).
    by rewrite big_split sum1_card /= subSKn addnK card_ord.
  by move=> i _; rewrite size_XsubC.
by move=> i _; rewrite polyXsubC_eq0.
Qed.

Lemma root_seq_nil (p : {poly F}) : (size p <= 1) = ((root_seq p) == [::]). 
Proof. by rewrite -subn_eq0 subn1 -size_root_seq size_eq0. Qed.

Lemma sub_root_div (p q : {poly F}) (Hq : q != 0) : 
  p %| q -> {subset (root_seq p) <= (root_seq q)} .
Proof.
case: (altP ((@eqP _ p 0)))=> [->|Hp]; first by rewrite root_seq0.
by case/dvdpP=> x Hx y; rewrite !root_root_seq // Hx rootM orbC=> ->. 
Qed.

Definition root_seq_uniq p := undup (root_seq p). 

Lemma prod_XsubC_count (p : {poly F}): 
   p = (lead_coef p) *: 
  \prod_(x <- root_seq_uniq p) ('X - x%:P)^+ (count (pred1 x) (root_seq p)).
Proof.
by rewrite {1}[p]root_seq_eq (prod_seq_count (root_seq p)).
Qed.

Lemma count_root_seq p x : count (pred1 x) (root_seq p) = \mu_x p.
Proof.
case: (altP (p =P 0))=> Hp; first by rewrite Hp root_seq0 mu0. 
apply/eqP; rewrite -muP //.
case H: (x \in root_seq p).
  rewrite -mem_undup in H.  
  have:= (prod_XsubC_count p).
  rewrite (bigD1_seq x) //= ?undup_uniq //.
  set b:= \big[_/_]_(_ <- _ | _) _ => Hpq.
  apply/andP; split; apply/dvdpP.
    by exists (lead_coef p *: b); rewrite -scalerAl mulrC.
  case=> q Hq.
  have H1: ~~ (('X - x%:P) %| b).
    rewrite dvdp_XsubCl; apply/rootP.
    rewrite horner_prod; apply/eqP. 
    rewrite (big_nth 0) big_mkord.  
    apply/prodf_neq0=> i Hix.
    by rewrite horner_exp hornerXsubC expf_neq0 // subr_eq0 eq_sym.
  have H2: (('X - x%:P) %| b).
    apply/dvdpP; exists ((lead_coef p)^-1 *: q).
    apply: (@scalerI _ _ (lead_coef p)); first by rewrite lead_coef_eq0.
    rewrite -scalerAl scalerA mulrV ?unitfE ?lead_coef_eq0 // scale1r. 
    have HX: (('X - x%:P)^+ (count (pred1 x) (root_seq p))) != 0.
      by apply: expf_neq0; rewrite -size_poly_eq0 size_XsubC.
    rewrite -(mulpK (_ *: b) HX) -(mulpK (q * _) HX).
    by rewrite -scalerAl mulrC -Hpq -mulrA -exprS -Hq.
  by rewrite H2 in H1.
have->: count (xpred1 x) (root_seq p) = 0%N.
  by apply/eqP; rewrite -leqn0 leqNgt -has_count has_pred1 H.
by rewrite dvd1p dvdp_XsubCl -root_root_seq // H.
Qed.

Definition root_mu_seq p := [seq (x,(\mu_x p)) | x <- (root_seq_uniq p)].

Lemma root_mu_seq_pos x p : p != 0 -> x \in root_mu_seq p -> 0 < x.2.  
Proof.
move=> Hp H.
have Hr: size (root_seq_uniq p) = size (root_mu_seq p) by rewrite size_map.
have Hs: index x (root_mu_seq p) < size (root_seq_uniq p).
  by rewrite Hr index_mem.
rewrite -(nth_index (0,0%N) H) // (nth_map 0) // mu_gt0 //. 
by rewrite -root_root_seq // -mem_undup mem_nth.
Qed.

Definition root_seq_poly (s : seq {poly F}) := flatten (map root_mu_seq s).

Lemma root_seq_poly_pos x s : (forall p , p \in s -> p !=0) -> 
  x \in root_seq_poly s -> 0 < x.2.
Proof.
elim : s=> [|p l IHl H]; first by rewrite in_nil.
rewrite mem_cat.
case/orP; first by apply: root_mu_seq_pos; apply: H; rewrite mem_head.
by apply: IHl=> q Hq; apply: H; rewrite in_cons Hq orbT.
Qed.

Definition linear_factor_seq p :=
   [seq ('X - x.1%:P)^+x.2 | x <- (root_mu_seq p)].

Lemma monic_linear_factor_seq p : forall q, q \in linear_factor_seq p -> 
  q \is monic.
Proof.
move=> q Hq; rewrite -(nth_index 0 Hq) (nth_map (0,0%N)).
apply: monic_exp; first by apply: monicXsubC.
by rewrite -index_mem size_map in Hq.
Qed.

Lemma size_linear_factor_leq1 p : forall q, q \in linear_factor_seq p ->
  1 < size q.
Proof.
move=> q; case: (altP (@eqP _ p 0))=> [Hp|Hp Hq].
  rewrite Hp /linear_factor_seq /root_mu_seq.
  by rewrite /root_seq_uniq /root_seq size_poly0.
rewrite -(nth_index 0 Hq) (nth_map (0,0%N)); last first.
  by rewrite -index_mem size_map in Hq.
rewrite size_exp_XsubC (nth_map 0); last first.
  by rewrite -index_mem !size_map in Hq.
rewrite -(@prednK (\mu_ _ _)) // mu_gt0 // -root_root_seq //.  
rewrite -mem_undup mem_nth //.
by rewrite -index_mem !size_map in Hq.
Qed.

Lemma coprimep_linear_factor_seq p :
  forall (i j : 'I_(size (linear_factor_seq p))),
  i != j ->
  coprimep (linear_factor_seq p)`_i (linear_factor_seq p)`_j.
Proof.
move=> [i Hi] [j Hj]; move: Hi Hj; rewrite !size_map=> Hi Hj Hij.
rewrite !(nth_map (0,0%N)) ?size_map //.
apply/coprimep_expl/coprimep_expr/coprimep_factor.
by rewrite unitfE subr_eq0 !(nth_map 0) //= nth_uniq // ?undup_uniq // eq_sym.
Qed.

Lemma prod_XsubC_mu (p : {poly F}): 
   p = (lead_coef p) *: \prod_(x <- root_seq_uniq p) ('X - x%:P)^+(\mu_x p).
Proof.
rewrite {1}[p]prod_XsubC_count.
by congr GRing.scale; apply: eq_bigr => i _; rewrite count_root_seq.
Qed.

Lemma monic_prod_XsubC p :
   p \is monic -> p = \prod_(x <- root_seq_uniq p) ('X - x%:P)^+(\mu_x p).
Proof.
by move/monicP=> H; rewrite {1}[p]prod_XsubC_mu H scale1r.
Qed.

Lemma prod_factor (p : {poly F}): 
   p = (lead_coef p) *: \prod_(x <- linear_factor_seq p) x.
Proof.
by rewrite !big_map {1}[p]prod_XsubC_mu.
Qed.

Lemma monic_prod_factor p :
   p \is monic -> p = \prod_(x <- linear_factor_seq p) x.
Proof.
by move/monicP=> H; rewrite {1}[p]prod_factor H scale1r.
Qed.

Lemma uniq_root_mu_seq (p : {poly F}) : uniq (root_seq p) -> 
  forall x, x \in root_mu_seq p -> x.2 = 1%N.
Proof.
move=> H x /(nthP (0,0%N)) [i]; rewrite size_map=> Hi.
rewrite (nth_map 0) // => <- /=; move: Hi.
rewrite /root_seq_uniq undup_id // -count_root_seq => Hi.
by rewrite count_uniq_mem // (mem_nth 0 Hi).
Qed.

Lemma uniq_root_dvdp p q : q != 0 ->
  (uniq (root_seq q)) -> p %| q -> (uniq (root_seq p)).
Proof.
move=> Hq Hq2 Hpq.
apply: count_mem_uniq=> x.
have Hc:= (count_uniq_mem x Hq2).
have Hle: count (pred1 x) (root_seq p) <= count (pred1 x) (root_seq q).
  rewrite !count_root_seq; case/dvdpP: Hpq => r Hr.
  by rewrite Hr mu_mul -?Hr // leq_addl.
have: count (pred1 x) (root_seq p) <= 1.
  by rewrite (leq_trans Hle) // Hc; case: (x \in root_seq q). 
rewrite leq_eqVlt ltnS leqn0.
case Hp: (x \in root_seq p).
  rewrite -has_pred1 has_count in Hp.
  by rewrite (eqn_leq _ 0%N) leqNgt Hp orbF => /eqP ->.
by rewrite eqn_leq -has_count has_pred1 Hp andbF orFb => /eqP ->.
Qed.

Lemma root_root_mu_seq p : [seq x.1 | x <- root_mu_seq p] = root_seq_uniq p.
Proof.
apply: (@eq_from_nth _ 0)=>[|i]; rewrite !size_map //.
by move=> Hi; rewrite (nth_map (0,0%N)) ?size_map // (nth_map 0) //.
Qed.

End poly_closedFieldType.

End Polynomial.

(****************************************************************************)
(****************************************************************************)
(************ left pseudo division, it is complement of polydiv. ************)
(****************************************************************************)
(****************************************************************************)
Import GRing.Theory.
Import Pdiv.Ring.
Import Pdiv.RingMonic.

Local Open Scope ring_scope.

Module RPdiv.

Section RingPseudoDivision.

Variable R : ringType.
Implicit Types d p q r : {poly R}.

Definition id_converse_def := (fun x : R => x : R^c).
Lemma add_id : additive id_converse_def.
Proof. by []. Qed.

Definition id_converse := Additive add_id.

Lemma expr_rev (x : R) k : (x : R^c) ^+ k = x ^+ k.
Proof. by elim:k=> // k IHk; rewrite exprS exprSr IHk. Qed.

Definition phi (p : {poly R}^c) := map_poly id_converse p.

Fact phi_is_rmorphism : rmorphism phi.
Proof.
split=> //; first exact:raddfB.
split=> [p q|]; apply/polyP=> i; last by rewrite coef_map !coef1.
by rewrite coefMr coef_map coefM; apply: eq_bigr => j _; rewrite !coef_map.
Qed.

Canonical phi_rmorphism := RMorphism phi_is_rmorphism.

Definition phi_inv (p : {poly R^c}) :=
  map_poly (fun x : R^c => x : R) p : {poly R}^c.

Lemma phiK : cancel phi phi_inv.
Proof. by move=> p; rewrite /phi_inv -map_poly_comp_id0 // map_poly_id. Qed.

Lemma phi_invK : cancel phi_inv phi.
Proof. by move=> p; rewrite /phi -map_poly_comp_id0 // map_poly_id. Qed.

Lemma phi_bij : bijective phi.
Proof. by exists phi_inv; first exact: phiK; exact: phi_invK. Qed.

Lemma monic_map_inj (aR rR : ringType) (f : aR -> rR) (p : {poly aR}) :
  injective f -> f 0 = 0 -> f 1 = 1 -> map_poly f p \is monic = (p \is monic).
Proof.
move=> inj_f eq_f00 eq_f11; rewrite !monicE lead_coef_map_inj ?rmorph0 //.
by rewrite -eq_f11 inj_eq.
Qed.

Definition redivp_l (p q : {poly R}) : nat * {poly R} * {poly R} :=
  let:(d,q,p) := (redivp (phi p) (phi q)) in
  (d, phi_inv q, phi_inv p).

Definition rdivp_l p q := ((redivp_l p q).1).2.
Definition rmodp_l p q := (redivp_l p q).2.
Definition rscalp_l p q := ((redivp_l p q).1).1.
Definition rdvdp_l p q := rmodp_l q p == 0.
Definition rmultp_l := [rel m d | rdvdp_l d m].

Lemma ltn_rmodp_l p q : (size (rmodp_l p q) < size q) = (q != 0).
Proof.
have := ltn_rmodp (phi p) (phi q).
rewrite -(rmorph0 phi_rmorphism) (inj_eq (can_inj phiK)) => <-.
rewrite /rmodp_l /redivp_l /rmodp; case: (redivp _ _)=> [[k q'] r'] /=.
by rewrite !size_map_inj_poly.
Qed.

End RingPseudoDivision.

Module mon.

Section MonicDivisor.

Variable R : ringType.
Implicit Types p q r : {poly R}.

Variable d : {poly R}.
Hypothesis mond : d \is monic.

Lemma rdivp_l_eq p : 
  p = d * (rdivp_l p d) + (rmodp_l p d).
Proof.
have mon_phi_d: phi d \is monic by rewrite monic_map_inj.
apply:(can_inj (@phiK R)); rewrite {1}[phi p](rdivp_eq mon_phi_d) rmorphD.
rewrite rmorphM /rdivp_l /rmodp_l /redivp_l /rdivp /rmodp.
by case: (redivp _ _)=> [[k q'] r'] /=; rewrite !phi_invK.
Qed.

End MonicDivisor.

End mon.

End RPdiv.

(****************************************************************************)
(****************************************************************************)
(****************************************************************************)
(****************************************************************************)
