(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path tuple.
From mathcomp Require Import perm fingroup choice ssralg fintype finfun poly polydiv.
From mathcomp Require Import bigop matrix zmodp mxalgebra.

Require Import ssrcomplements dvdring mxstructure similar minor binetcauchy.
Require Import stronglydiscrete.
Require Import coherent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(** Elementary divisor rings *)
Module EDR.

Variant smith_spec (R : dvdRingType) m n M
  : 'M[R]_m * seq R * 'M[R]_n -> Type :=
    SmithSpec P d Q of P *m M *m Q = diag_mx_seq m n d
                     & sorted %|%R d
                     & P \in unitmx
                     & Q \in unitmx : smith_spec M (P,d,Q).

Record mixin_of (R : dvdRingType) : Type := Mixin {
  smith : forall m n, 'M[R]_(m,n) -> 'M[R]_m * seq R * 'M[R]_n;
  _ : forall m n (M : 'M[R]_(m,n)), smith_spec M (smith M)
}.

Section ClassDef.

(** EDRs are based on dvdrings *)
Record class_of (R : Type) : Type := Class {
  base  : DvdRing.class_of R;
  mixin : mixin_of (DvdRing.Pack base)
}.
Local Coercion base : class_of >-> DvdRing.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@DvdRing.Pack T b0)) :=
  fun bT b & phant_id (DvdRing.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) .

Definition eqType := Equality.Pack class.
Definition choiceType := Choice.Pack class.
Definition zmodType := GRing.Zmodule.Pack class.
Definition ringType := GRing.Ring.Pack class.
Definition comRingType := GRing.ComRing.Pack class.
Definition unitRingType := GRing.UnitRing.Pack class.
Definition comUnitRingType := GRing.ComUnitRing.Pack class.
Definition idomainType := GRing.IntegralDomain.Pack class.
Definition dvdRingType := DvdRing.Pack class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> DvdRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion dvdRingType : type >-> DvdRing.type.
Canonical Structure dvdRingType.

Notation edrType := type.
Notation EDRType T m := (@pack T _ m _ _ id _ id).
Notation EDRMixin := Mixin.
Notation "[ 'edrType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'edrType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'edrType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'edrType'  'of'  T ]") : form_scope.
End Exports.

End EDR.
Export EDR.Exports.

Definition smith R := EDR.smith (EDR.class R).
Definition smith_spec := EDR.smith_spec.

Section EDR_Theory.

Variable R : edrType.

Lemma smithP : forall m n (M : 'M[R]_(m,n)), smith_spec M (smith M).
Proof. by case: R=> [? [? []]]. Qed.

Definition smith_seq m n (M : 'M[R]_(m,n)) := (smith M).1.2.

(* EDRs are gcd domains *)
Definition gcd_edr a b : R := (smith_seq (row_mx a%:M b%:M : 'rV_2))`_0.

Arguments nth : simpl never.

Lemma gcd_edrP d a b :
  (d %| gcd_edr a b)%R = (d %| a)%R && (d %| b)%R.
Proof.
rewrite /gcd_edr /smith_seq; case: smithP => /= P ds Q heq _ Punitmx Qunitmx.
apply/idP/andP => [gd0|[gdvda gdvdb]].
  suff Hij : forall i j, d %| (row_mx a%:M b%:M : 'rV_2) i j.
    move: (Hij 0 (@lshift 1 1 0)) (Hij 0 (rshift 1 0)).
    by rewrite (row_mxEl a%:M) (row_mxEr a%:M) !mxE !mulr1n.
  move/(canRL (mulmxK Qunitmx))/(canRL (mulKmx Punitmx)): heq ->.
  apply/dvdr_mulmxl/dvdr_mulmxr=> i j.
  by rewrite ord1 {i} mxE; case: j => [[]] //= _ _; rewrite mulr0n dvdr0.
move/matrixP: heq => /(_ 0 0).
rewrite [P]mx11_scalar mul_scalar_mx !mxE big_ord_recl big_ord1 -rshift1 mulr1n.
have -> : ord0 = 0 by [].
rewrite -(lshift0 1 0) mxE (row_mxEl a%:M) 2!mxE (row_mxEr a%:M) => <-.
by rewrite -!mulrA -mulrDr dvdr_mull // dvdr_add ?dvdr_mulr ?mxE.
Qed.

Definition gcdMixin := GcdDomain.Mixin gcd_edrP.
Canonical gcdType   := Eval hnf in GcdDomainType R gcdMixin.

(** The existence of an algorithm computing Smith normal form implies
the the ring is a Bézout domain *)
Definition bezout_edr a b : R * R :=
  let: (P,d,Q) := smith (row_mx a%:M b%:M : 'rV_2)
  in (P 0 0 * Q 0 0, P 0 0 * Q (rshift 1 0) 0).

Lemma bezout_edrP a b : BezoutDomain.bezout_spec a b (bezout_edr a b).
Proof.
have := erefl (gcd_edr a b); rewrite {-1}/gcd_edr /smith_seq.
rewrite /bezout_edr; case: smithP => /= P d Q heq hsorted Punitmx Qunitmx hg.
constructor; rewrite /gcdr /= hg.
move/matrixP: (heq) => /(_ 0 0).
rewrite [P]mx11_scalar mul_scalar_mx !mxE big_ord_recl big_ord1 -rshift1 mulr1n.
have -> : ord0 = 0 by [].
rewrite -{1}(lshift0 1 0) mxE (row_mxEl a%:M) 2!mxE (row_mxEr a%:M) !mxE !mulr1n.
by rewrite mulrAC [_ * b * _]mulrAC=> ->.
Qed.

Definition bezoutMixin := BezoutDomainMixin bezout_edrP.
Canonical bezoutType   := Eval hnf in BezoutDomainType R bezoutMixin.

(* Hence are EDRs also strongly discrete *)
Definition stronglyDiscreteMixin := bezout_stronglyDiscreteMixin [bezoutDomainType of R].
Canonical stronglyDiscreteType   := Eval hnf in StronglyDiscreteType R stronglyDiscreteMixin.

(* As we have a Smith normal form algorithm we can compute ker and coker *)
Section snf_coherent.

Section defs.

Variable m n : nat.
Variable M : 'M[R]_(m,n).

Definition col_ebase := invmx (smith M).1.1.
Definition row_ebase := invmx (smith M).2.

(* Filter out all trailing zeroes *)
Definition diag      := [seq x <- take (minn m n) (smith_seq M) | x != 0 ].
Definition diag_mx   := diag_mx_seq m n diag.

(* Note: The matrix rank is NOT the module rank! *)
Definition mxrank := size diag.

Definition kermx   : 'M_m := copid_mx mxrank *m invmx col_ebase.
Definition cokermx : 'M_n := invmx row_ebase *m copid_mx mxrank.

End defs.

Lemma mulmx_ebase m n (M : 'M_(m, n)) :
  col_ebase M *m diag_mx M *m row_ebase M = M.
Proof.
rewrite /col_ebase /diag_mx /row_ebase /diag /smith_seq.
case: smithP => /= L0 d R0 h1 h2 L0unit R0unit.
rewrite diag_mx_seq_filter0 ?(sorted_take (@dvdr_trans R)) // diag_mx_seq_take_min.
by rewrite -h1 !mulmxA mulVmx // mul1mx -mulmxA mulmxV ?mulmx1.
Qed.

Lemma diag_neq0 m n (M : 'M[R]_(m,n)) i (his : i < size (diag M)) :
  (diag M)`_i != 0.
Proof.
exact: (all_nthP 0 (filter_all (fun x => x != 0) (take _ (smith M).1.2))).
Qed.

Lemma row_ebase_unit m n (M : 'M_(m, n)) : row_ebase M \in unitmx.
Proof. by rewrite unitmx_inv; case: smithP. Qed.

Lemma col_ebase_unit m n (M : 'M_(m, n)) : col_ebase M \in unitmx.
Proof. by rewrite /col_ebase unitmx_inv; case: smithP. Qed.

Lemma mulmx_diag_mx m n (M : 'M_(m, n)) :
  diag_mx M = invmx (col_ebase M) *m M *m invmx (row_ebase M).
Proof.
rewrite /col_ebase /diag_mx /row_ebase /diag /smith_seq !invmxK.
case: smithP=> L0 d R0 h1 h2 _ _.
rewrite diag_mx_seq_filter0; last exact: (sorted_take (@dvdr_trans R)).
by rewrite diag_mx_seq_take_min.
Qed.

Lemma mul_kermx m n (M : 'M_(m, n)) : kermx M *m M = 0.
Proof.
rewrite -{2}[M]mulmx_ebase !mulmxA mulmxKV ?col_ebase_unit //.
by rewrite mul_copid_mx_diag ?mul0mx // geq_min /mxrank leqnn orbT.
Qed.

Lemma diag0 m n : diag (0 : 'M[R]_(m,n)) = [::].
Proof.
rewrite /diag /smith_seq; case: smithP=> /= P d Q.
rewrite mulmx0 mul0mx => /esym h0 _ _ _.
have H : all (eq_op^~ 0) (take (minn m n) d).
  apply: (@diag_mx_seq_eq0 _ m n); first by rewrite size_take; case: leqP.
  by rewrite diag_mx_seq_take_min.
by elim: (take (minn m n) d) H => //= a l h /andP [->] /=.
Qed.

Lemma mxrank0 m n : mxrank (0 : 'M[R]_(m,n)) = 0%N.
Proof. by rewrite /mxrank diag0. Qed.

Lemma mxrank_leq_col_row : forall m n (M : 'M_(m, n)), mxrank M <= minn m n.
Proof.
case => [|m] [|n] //= M; rewrite ?(thinmx0,flatmx0,mxrank0,leq0n) //.
rewrite /mxrank size_filter /smith_seq /=; case: smithP => /= P d Q _ _ _ _.
by apply/(leq_trans (count_size _ _)); rewrite size_take; case: leqP.
Qed.

Lemma mxrank_leq_row m n (M : 'M_(m, n)) : mxrank M <= m.
Proof. by move: (mxrank_leq_col_row M); rewrite leq_min; case/andP. Qed.

Lemma mxrank_leq_col m n (M : 'M_(m, n)) : mxrank M <= n.
Proof. by move: (mxrank_leq_col_row M); rewrite leq_min; case/andP. Qed.

Lemma mulmx_coker m n (M : 'M_(m, n)) : M *m cokermx M = 0.
Proof.
rewrite -{1}[M]mulmx_ebase -!mulmxA mulKVmx ?row_ebase_unit //.
by rewrite mul_diag_mx_copid ?mulmx0 // geq_min leqnn orbT.
Qed.

Lemma mulmxKV_kermx m n p (M : 'M_(n, p)) (N : 'M_(m, n)) :
  N *m M = 0 -> N *m col_ebase M *m kermx M = N.
Proof.
rewrite mulmxA mulmxBr mulmx1 mulmxBl mulmxK ?col_ebase_unit //.
rewrite -{1}[M]mulmx_ebase !mulmxA.
move/(canRL (mulmxK (row_ebase_unit M))); rewrite mul0mx // => BA0.
apply: (canLR (addrK _)); rewrite -(pid_mx_id _ _ n (mxrank_leq_col M)) mulmxA.
move/eqP: BA0; rewrite /diag_mx /mxrank.
by move/(mul_diag_mx_seq_eq0 (@diag_neq0 _ _ M))/eqP ->; rewrite !mul0mx addr0.
Qed.

Lemma kermxP m n (M : 'M[R]_(m,n)) (X : 'rV_m) :
  reflect (exists Y : 'rV_m, X = Y *m kermx M) (X *m M == 0).
Proof.
apply: (iffP eqP)=> [|[Y ->]]; last by rewrite -mulmxA mul_kermx mulmx0.
by move/mulmxKV_kermx=> hX; exists (X *m col_ebase M).
Qed.

Definition coherentMixin := CoherentRing.Mixin kermxP.
Canonical coherentType   := Eval hnf in CoherentRingType R coherentMixin.

End snf_coherent.

(** Beginning of unicity *)
Section Preunicity.

Variables (s : seq R) (m n k : nat) (A : 'M[R]_(m,n)).

Hypothesis (Hk : k <= minn m n) (Hs: sorted %|%R s).
Hypothesis (HAs : equivalent A (diag_mx_seq m n s)).

Let widen_minl i := widen_ord (geq_minl m n) i.
Let widen_minr i := widen_ord (geq_minr m n) i.

Lemma minor_diag_mx_seq :
  forall (f g : 'I_k -> 'I_(minn m n)),
  injective f -> injective g -> {subset codom f <= codom g} ->
    minor (widen_minl \o f) (widen_minr \o g) (diag_mx_seq m n s) %=
    \prod_i s`_(f i).
Proof.
elim: k=>[f g|j IHj f g Hf Hg Hfg]; first by rewrite /minor det_mx00 big_ord0.
have: perm_eq [seq f x | x in 'I_j.+1] [seq g x | x in 'I_j.+1].
  have [||_ e] := uniq_min_size _ Hfg; first by rewrite map_inj_uniq ?enum_uniq.
    by rewrite !size_map.
  by rewrite uniq_perm // map_inj_uniq // enum_uniq.
have Ht : size (codom g) == j.+1 by rewrite size_codom card_ord.
have -> : image g 'I_j.+1 = Tuple Ht by [].
case/tuple_permP=> p Hp .
have Hfg0 i : g (p i) = f i.
  have He : i < #|'I_j.+1| by rewrite card_ord.
  have {2}-> : i = enum_val (Ordinal He) by rewrite enum_val_ord; apply: ord_inj.
  rewrite -(nth_image (f ord0)) Hp -tnth_nth tnth_mktuple (tnth_nth (f ord0)).
  by rewrite /= codomE (nth_map ord0) ?nth_ord_enum // size_enum_ord.
rewrite /minor (expand_det_row _ ((p^-1)%g ord0)) big_ord_recl big1=>[|i _]; last first.
  rewrite !mxE /= (inj_eq (@ord_inj _)) -Hfg0 (inj_eq Hg) permKV.
  by rewrite (negbTE (neq_lift _ _)) mul0r.
rewrite /cofactor !mxE /=; set B := diag_mx_seq _ _ _; set M := row' _ _.
set p0 := ((p^-1)%g ord0).
pose f2 x := f (lift p0 x); pose g2 x := g (lift ord0 x).
have Hf2 : injective f2 by apply/(inj_comp Hf)/lift_inj.
have Hg2 : injective g2 by apply/(inj_comp Hg)/lift_inj.
pose f' i := widen_ord (geq_minl m n) (f2 i).
pose g' i := widen_ord (geq_minr m n) (g2 i).
have -> : M = submatrix f' g' B by apply/matrixP=> r t; rewrite !mxE.
have Hfg2 : {subset codom f2 <= codom g2}.
  move=> x /codomP [y ->].
  rewrite codomE /f2 /g2 -Hfg0 map_comp (mem_map Hg).
  have: p (lift p0 y) \in enum 'I_j.+1 by rewrite mem_enum.
  rewrite enum_ordS in_cons -(permKV p ord0).
  by rewrite (inj_eq (@perm_inj _ _)) eq_sym (negbTE (neq_lift _ _)).
rewrite addr0 (bigD1 ((p^-1)%g ord0)) //= -Hfg0 permKV eqxx eqd_mull //.
rewrite -[X in _ %= X]mul1r eqd_mul ?eqd1 ?unitrX ?unitrN ?unitr1 //.
rewrite (eq_bigl (fun i => p0 != i)); last by move=> i /=; rewrite eq_sym.
apply: (eqd_trans (IHj _ _ Hf2 Hg2 Hfg2)); apply: eq_eqd; rewrite /f2.
case: (pickP 'I_j) => [k0 _ | n0]; last first.
  by rewrite !big1 // => [k' /unlift_some[i] | i _]; have:= n0 i.
rewrite (reindex (lift p0)); first by apply: eq_bigl=> k'; rewrite neq_lift.
exists (fun k => odflt k0 (unlift p0 k)) => k'; first by rewrite liftK.
by case/unlift_some=> k'' -> ->.
Qed.

Lemma prod_minor_seq :
  \prod_(i < k) s`_i =
   minor [ffun x : 'I_k => widen_minl (widen_ord Hk x)]
         [ffun x : 'I_k => widen_minr (widen_ord Hk x)] (diag_mx_seq m n s).
Proof.
rewrite /minor /submatrix.
elim: k Hk=>[H|j /= IHj Hj]; first by rewrite det_mx00 big_ord0.
have IH : j <= (minn m n) by apply: ltnW.
apply: esym; rewrite (expand_det_row _ ord_max) big_ord_recr /=.
rewrite big1 ?add0r /cofactor=> [|i _]; last first.
  by rewrite !mxE !ffunE eqn_leq leqNgt (ltn_ord i) andFb mul0r.
rewrite !mxE !ffunE eqxx exprD -expr2 sqrr_sign mul1r.
rewrite /row' /col'; set M := matrix_of_fun _ _.
rewrite big_ord_recr /= (IHj IH) mulr1n mulrC; do 2!f_equal.
apply/matrixP=> i l; rewrite !mxE !ffunE /= /bump.
by do 2!rewrite leqNgt (ltn_ord _) add0n.
Qed.

Lemma minor_eq0l (R' : comRingType) k1 m1 n1 (s1 : seq R') x :
  forall (f : 'I_k1 -> 'I_m1) g, n1 <= f x ->
  minor f g (diag_mx_seq m1 n1 s1) = 0.
Proof.
move=> f g H; rewrite /minor (expand_det_row _ x) big1 // => i _.
by rewrite !mxE gtn_eqF ?mul0r // (leq_trans _ H).
Qed.

Lemma minor_eq0r (R' : comRingType) k1 m1 n1 (s1 : seq R') x :
  forall f (g : 'I_k1 -> 'I_n1) , m1 <= g x ->
  minor f g (diag_mx_seq m1 n1 s1) = 0.
Proof.
move=> f g H; rewrite /minor (expand_det_col _ x) big1 // => i _.
by rewrite !mxE ltn_eqF ?mul0r // (leq_trans _ H).
Qed.

Lemma eqd_seq_gcdr :
  \prod_(i < k) s`_i %=
  \big[(@gcdr gcdType)/0]_(f : {ffun 'I_k -> 'I_m})
  (\big[(@gcdr gcdType)/0]_(g : {ffun 'I_k -> 'I_n}) minor f g (diag_mx_seq m n s)).
Proof.
apply/andP; split; last first.
  rewrite prod_minor_seq; set j := [ffun _ => _].
  by apply/(dvdr_trans (big_dvdr_gcdr _ j))/big_dvdr_gcdr.
apply: big_gcdrP=> f; apply: big_gcdrP=> g.
case: (injectiveb f) /injectiveP=> Hinjf; last first.
  by rewrite (minor_f_not_injective _ _ Hinjf) dvdr0.
case: (injectiveb g) /injectiveP=> Hinjg; last first.
  by rewrite (minor_g_not_injective _ _ Hinjg) dvdr0.
have Hmin k1 i m1 n1 (h : 'I_k1 -> 'I_m1) : minn m1 n1 <= h i -> n1 <= h i.
  move=> Hhi; have := (leq_ltn_trans Hhi (ltn_ord (h i))).
  by rewrite gtn_min ltnn=> /ltnW/minn_idPr <-.
case/altP: (@forallP _ (fun i => f i < minn m n)) => [Hwf|]; last first.
  rewrite negb_forall=> /existsP [x]; rewrite -leqNgt=> /Hmin Hx.
  by rewrite (minor_eq0l _ _ Hx) dvdr0.
case/altP: (@forallP _ (fun i => g i < minn m n)) => [Hwg|]; last first.
  rewrite negb_forall=> /existsP [x]; rewrite -leqNgt minnC=> /Hmin Hx.
  by rewrite (minor_eq0r _ _ Hx) dvdr0.
pose f1 i := Ordinal (Hwf i).
pose g1 i := Ordinal (Hwg i).
have Hinjf1 : injective f1.
  by move=> x y /eqP; rewrite -(inj_eq (@ord_inj _)) /= => /eqP/ord_inj/Hinjf.
have Hinjg1 : injective g1.
  by move=> x y /eqP; rewrite -(inj_eq (@ord_inj _)) /= => /eqP/ord_inj/Hinjg.
case Hcfg: (codom f1 \subset codom g1); last first.
  move/negbT: Hcfg=> /subsetPn [x] /codomP [y Hy] /negP Habs.
  rewrite /minor (expand_det_row _ y).
  rewrite [\sum_(_ <_) _](big1 _ xpredT) ?dvdr0 //.
  move=> j _; rewrite !mxE.
  have ->: (g j = g1 j :> nat) by [].
  have ->: (f y = f1 y :> nat) by [].
  have ->: (f1 y == g1 j :> nat) = false.
    by apply/negbTE/eqP=> /ord_inj=> H; apply: Habs; rewrite Hy H codom_f.
  by rewrite mul0r.
move/subsetP: Hcfg=> Hcfg.
pose f' i := widen_minl (f1 i).
pose g' i := widen_minr (g1 i).
have ->: minor f g (diag_mx_seq m n s) =
           minor f' g' (diag_mx_seq m n s).
  by apply: minor_eq=> i; apply: ord_inj.
rewrite (eqd_dvdr _ (minor_diag_mx_seq Hinjf1 Hinjg1 Hcfg)) //.
move: Hinjf1; clear -Hs; move: f1; clear -Hs.
elim: k =>[?|j /= IHj g Hg].
  by rewrite big_ord0 dvd1r.
rewrite big_ord_recr /=.
pose max:= \max_i (g i).
have [l Hl]: {j | max = g j} by apply: eq_bigmax; rewrite card_ord.
pose p := tperm l ord_max.
set B := \prod_(_ < _) _.
rewrite (reindex_inj (@perm_inj _ p)) /= big_ord_recr /= dvdr_mul //.
  pose f := (g \o p \o (widen_ord (leqnSn j))).
  have Hf: injective f.
    apply: inj_comp=> [|x y /eqP].
      by apply: inj_comp=> //; exact: perm_inj.
    by rewrite -(inj_eq (@ord_inj _)) /= => H; apply/ord_inj/eqP.
  have Hi: injective (finfun f).
    by move=> x e; rewrite !ffunE; exact: Hf.
  set C := \prod_(_ < _) _.
  have:= (IHj _ Hi).
  have ->: C = \prod_i s`_(finfun f i).
    by apply: eq_bigr=> i _; rewrite ffunE.
  by apply.
move: (sorted_nth0 (sorted_drop j Hs) (g (p ord_max) - j)).
rewrite !nth_drop addn0 subnKC //= tpermR; case/orP: (leq_total j (g l))=> //.
rewrite leq_eqVlt => /orP [|Hgm]; first by move/eqP=> ->; rewrite leqnn.
have Habs: forall i, g i < j.
  move=> i; apply: (leq_ltn_trans _ Hgm).
  by rewrite -Hl /k; exact: (leq_bigmax i).
pose f := fun x => Ordinal (Habs x).
have Hf: injective f.
  move=> x y /eqP; rewrite -(inj_eq (@ord_inj _)) /= => /eqP Hxy.
  by apply/Hg/ord_inj.
have: #|'I_j.+1| <= #|'I_j|.
  by rewrite -(card_codom Hf); exact: max_card.
by rewrite !card_ord ltnn.
Qed.

Lemma Smith_gcdr_spec :
  \prod_(i < k) s`_i %=
  \big[(@gcdr gcdType)/0]_(f : {ffun 'I_k -> 'I_m})
   (\big[(@gcdr gcdType)/0]_(g : {ffun 'I_k -> 'I_n}) minor f g A) .
Proof.
rewrite (eqd_ltrans eqd_seq_gcdr).
have [ _ _ [M [N [_ _ Heqs]]]] := HAs.
have [ _ _ [P [Q [_ _ Hseq]]]] := equiv_sym HAs.
rewrite conform_mx_id in Heqs.
rewrite conform_mx_id in Hseq.
have HdivmA p q k1 (B C : 'M[R]_(p,q)) (M1 : 'M_p) (N1 : 'M_q) :
   forall (H : M1 *m C *m N1 = B),
   forall (f : 'I_k1 -> 'I_p) (g : 'I_k1 -> 'I_q),
   \big[(@gcdr gcdType)/0]_(f0 : {ffun 'I_k1 -> 'I_p})
    \big[(@gcdr gcdType)/0]_(g0 : {ffun 'I_k1 -> 'I_q}) minor f0 g0 C
    %| minor f g B.
  move=> H f g.
  have HBC: minor f g B =  \sum_(f0 : {ffun 'I__ -> 'I__ } | strictf f0)
                 ((\sum_(g0 : {ffun 'I__ -> 'I__ } | strictf g0)
                  (minor id g0 (submatrix f id M1) * minor g0 f0 C)) *
                   minor f0 id (submatrix id g N1)).
    rewrite -H /minor submatrix_mul BinetCauchy.
    apply: eq_bigr=> i _; congr GRing.mul; rewrite /minor.
    rewrite sub_submatrix submatrix_mul BinetCauchy.
    by apply: eq_bigr=> j _; rewrite /minor !sub_submatrix.
  rewrite HBC; apply: big_dvdr=> h; rewrite dvdr_mulr //.
  apply: big_dvdr=> j; rewrite dvdr_mull //.
  by apply: (dvdr_trans (big_dvdr_gcdr _ j)); apply: big_dvdr_gcdr.
apply/andP; split; apply: big_gcdrP=> f; apply: big_gcdrP=> g.
  exact: (HdivmA _ _ _ _ _ _ _ Hseq).
exact: (HdivmA _ _ _ _ _ _ _ Heqs).
Qed.

End Preunicity.

Section Unicity.

Lemma Smith_unicity m n (M : 'M[R]_(m,n)) (d : seq R) :
  sorted %|%R d -> equivalent M (diag_mx_seq m n d) ->
  forall i, i < minn m n -> d`_i %= (smith_seq M)`_i.
Proof.
rewrite /smith_seq=> Hd HMd i.
case: smithP=> P s Q heq Hsorted Punitmx Qunitmx /=.
have HMdmt : equivalent M (diag_mx_seq m n s).
  by split=> //; exists P; exists Q; split=> //; rewrite conform_mx_id.
elim: i {-2}i (leqnn i)=>[i|i IHi j Hji Hj].
  rewrite leqn0=> /eqP -> Hi.
  move: (Smith_gcdr_spec Hi Hd HMd); rewrite eqd_sym.
  move/(eqd_trans (Smith_gcdr_spec Hi Hsorted HMdmt)).
  by rewrite !big_ord1 eqd_sym.
move: (Smith_gcdr_spec Hj Hd HMd); rewrite eqd_sym.
move/(eqd_trans (Smith_gcdr_spec Hj Hsorted HMdmt)).
rewrite !big_ord_recr /= => H3.
have H1: \prod_(i < j) d`_i %= \prod_(i < j) s`_i.
  apply: eqd_big_mul=> k _.
  by rewrite (IHi k _ (ltn_trans _ Hj)) // -ltnS (leq_trans (ltn_ord k) Hji).
have [H0|H0] := boolP (\prod_(i < j) d`_i == 0).
  have/prodf_eq0 [k _ /eqP Hk] : (\prod_(i < j) s`_i == 0).
    by rewrite (eqP H0) eqd0r in H1.
  case/prodf_eq0: H0 => l _ /eqP Hl.
  move: (sorted_nth0 (sorted_drop k Hsorted) (j - k)).
  move: (sorted_nth0 (sorted_drop l Hd) (j - l)).
  rewrite !nth_drop !addn0 Hk Hl !dvd0r (subnKC (ltnW (ltn_ord k))).
  by rewrite (subnKC (ltnW (ltn_ord l)))=> /eqP -> /eqP ->.
by rewrite -(eqd_mul2l _ _ H0) (eqd_rtrans (eqd_mulr _ H1)) eqd_sym.
Qed.

End Unicity.
End EDR_Theory.
