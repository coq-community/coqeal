From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_fingroup.
From mathcomp Require Import all_real_closed.
From CoqEAL Require Import binetcauchy ssrcomplements mxstructure minor.
From CoqEAL Require Import smith dvdring polydvd.
From CoqEAL Require Import similar perm_eq_image.

(**    This file is a complement of the file Smith.v of the CoqEAL library.
       We prove here the unicity of the Smith normal form of a matrix.

       The algorithm described in the file Smith.v takes a matrix M of
       type 'M_(m,n) and returns a triple (L,s,R) where s is the
       sequence such that diag_mx_seq m n s is the Smith normal
       form of M, and L and R are the transition matrices
       (i.e diag_mx_seq m n s = L * M * R). In this context we have
       the following definitions :

             Smith_seq M == The sequence s of the triple (L,s,R).
            Smith_form M == diag_mx_seq m n (Smith_seq M).


*)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Specification.

Import GRing.Theory.
Local Open Scope ring_scope.
Variable E : euclidDomainType.

Definition find1 m n (A : 'M[E]_(m.+1, n.+1)) (v : E) : option 'I_m :=
  pick [pred i | ~~(v %| A (lift 0 i) 0)].

Lemma find1P m n (A : 'M[E]_(m.+1, n.+1)) (v : E) :
  pick_spec [pred i | ~~(v %| A (lift 0 i) 0)] (find1 A v).
Proof. exact: pickP. Qed.

Definition find2 m n (A : 'M[E]_(m.+1, n.+1)) (v : E) :
    option ('I_m.+1 * 'I_n) :=
  pick [pred ij | ~~(v %| A ij.1 (lift 0 ij.2))] .

Lemma find2P m n (A : 'M[E]_(m.+1, n.+1)) v :
  pick_spec [pred ij | ~~(v %| A ij.1 (lift 0 ij.2))] (find2 A v).
Proof.  exact: pickP. Qed.

Definition find_pivot m n (A : 'M[E]_(m.+1, n.+1)) :
    option ('I_m.+1 * 'I_n.+1) :=
  pick [pred ij | A ij.1 ij.2 != 0].

Lemma find_pivotP m n (A : 'M[E]_(m.+1, n.+1)) :
  pick_spec [pred ij | A ij.1 ij.2 != 0] (find_pivot A).
Proof. exact: pickP. Qed.

Definition Smith_seq n m (M: 'M[E]_(n,m)) :=
  let: (L,d,R) := (Smith find1 find2 find_pivot M) in
  if d is a :: d' then (\det L)^-1 * (\det R)^-1 *a :: d' else nil.

Definition Smith_form n m (M: 'M[E]_(n,m)) :=
  diag_mx_seq n m (Smith_seq M).

Lemma equiv_Smith n m (M: 'M[E]_(n,m)) : equivalent M (Smith_form M).
Proof.
case: n m M=>[m M|n]; first exact: equiv0l.
case=>[M|m M]; first exact: equiv0r.
rewrite /Smith_form /Smith_seq.
case: (SmithP find1P find2P find_pivotP) => L0 d R0 H _ HL0 HR0; split=> //.
exists ((@block_mx _ 1 _ 1 _ ((\det L0)^-1 / \det R0)%:M 0 0 1%:M) *m L0).
exists R0; split=> //.
  rewrite unitmxE detM unitrM (@det_lblock _ 1 n) det_scalar1 det1 mulr1.
  by rewrite unitrM !unitrV -!unitmxE HL0 HR0.
rewrite conform_mx_id -!mulmxA (mulmxA L0) H.
case: d H =>[|a l _] ; first by rewrite !diag_mx_seq_nil mulmx0.
rewrite !diag_mx_seq_cons (@mulmx_block _ 1 _ 1 _ 1).
by rewrite !mulmx0 !mul0mx !add0r addr0 mul1mx -scalar_mxM.
Qed.

Lemma sorted_Smith n m (M: 'M[E]_(n,m)): 
  sorted (@dvdr E) (Smith_seq M).
Proof. 
rewrite /Smith_seq.
case: (SmithP find1P find2P find_pivotP) => L0 d R0 _ H HL0 HR0.
case: d H=> // a l /= H.
have/allP Ha: all (%|%R a) l by exact: (order_path_min (@dvdr_trans _)). 
rewrite path_min_sorted; [exact: (path_sorted H) | apply/allP=> x Hx].
apply/(dvdr_trans _ (Ha x Hx))/dvdrP; exists (\det R0 * \det L0). 
by rewrite -invrM ?mulVKr // unitrM -!unitmxE HR0.
Qed.

Lemma det_Smith n (M: 'M[E]_n) : \det (Smith_form M) = \det M.
Proof.
rewrite /Smith_form /Smith_seq.
case: n M=>[M|n M]; first by rewrite !det_mx00.
case: (SmithP find1P find2P find_pivotP)=> L0 d R0 H _ HL0 HR0.
case: d H=>[|a l].
  rewrite !diag_mx_seq_nil -{1}(mul0mx _ R0)=> /(mulIr HR0).
  by rewrite -{1}(mulmx0 _ L0)=> /(mulrI HL0)=> ->.
rewrite !diag_mx_seq_cons (@det_ublock _ 1) scalar_mxM detM -mulrA.
rewrite -(det_ublock a%:M 0)=> <-.
rewrite !detM -invrM -?unitmxE // det_scalar1 (mulrC (\det L0)).
rewrite -mulrA mulrC -(mulrA (\det M)) (mulrC (\det L0)) mulrV ?mulr1 //.
by rewrite unitrM -!unitmxE HR0.
Qed.

Lemma size_Smith_seq n (M: 'M[E]_n) : 
\det M != 0 -> size (take n (Smith_seq M)) = n.
Proof.
move/negbTE=> HdM0; rewrite size_take; case: ifP=> //.
move/negbT; rewrite -leqNgt leq_eqVlt; case/orP=> [/eqP -> //|].
rewrite ltnNge=> /negbTE H.
have:= (det_Smith M).
rewrite /Smith_form det_diag_mx_seq_truncated H=> /eqP.
by rewrite eq_sym HdM0. 
Qed.

End Specification.

Section Preunicity.

Import GRing.Theory.
Import PolyPriField.

Variable E : euclidDomainType.
Variables (s : seq E) (m n k : nat) (A : 'M[E]_(m,n)). 

Hypothesis (Hk : (k <= minn m n)%N) (Hs: sorted %|%R s).
Hypothesis (HAs : equivalent A (diag_mx_seq m n s)).

Let widen_minl i := widen_ord (geq_minl m n) i.
Let widen_minr i := widen_ord (geq_minr m n) i.

Lemma minor_diag_mx_seq :
  let l := minn m n in 
  forall (f g : 'I_k -> 'I_l),
  let f' i := widen_minl (f i) in
  let g' i := widen_minr (g i) in
  injective f -> injective g -> {subset codom f <= codom g} ->
  minor f' g' (diag_mx_seq m n s) %= \prod_i s`_(f i).
Proof.
rewrite /minor.
elim: k=>[f g|j IHj f g Hf Hg Hfg]; first by rewrite det_mx00 big_ord0.
have := perm_eq_image Hf Hg Hfg.
have Ht : size (codom g) == j.+1 by rewrite size_codom card_ord.
have -> : image g (ordinal_finType j.+1) = Tuple Ht by [].
case/tuple_permP=> p Hp.
have Hfg0 i : g (p i) = f i.
  have He: (i < #|'I_j.+1|)%N by rewrite card_ord.
  have {2}->: i = enum_val (Ordinal He) by rewrite enum_val_ord; apply: ord_inj.
  rewrite -(nth_image (f ord0)) Hp -tnth_nth tnth_mktuple (tnth_nth (f ord0)).
  by rewrite /= codomE (nth_map ord0) ?nth_ord_enum // size_enum_ord.
rewrite (expand_det_row _ ((p^-1)%g ord0)) big_ord_recl big1=>[|i _].
  rewrite /cofactor !mxE.
  set B := diag_mx_seq _ _ _.
  set M := row' _ _.
  pose f2 x :=  f (lift ((p^-1)%g ord0) x).
  pose g2 x :=  g (lift ord0 x).
  have Hf2: injective f2.
   by apply/(inj_comp Hf)/lift_inj.   
  have Hg2: injective g2.
   by apply/(inj_comp Hg)/lift_inj.      
  pose f' i := widen_ord (geq_minl m n) (f2 i).
  pose g' i := widen_ord (geq_minr m n) (g2 i).
  have ->: M = submatrix f' g' B.     
    by apply/matrixP=> r t; rewrite !mxE.
  have Hfg2: {subset codom f2 <= codom g2}.
    move=> x /codomP [y ->].
    rewrite codomE /f2 /g2 -Hfg0 map_comp (mem_map Hg).
    set i := p _.
    have:= mem_ord_enum i.
    rewrite -enum_ord_enum enum_ordS in_cons -(permKV p ord0).
    by rewrite /i (inj_eq (@perm_inj _ _)) eq_sym (negbTE (neq_lift _ _)).
  rewrite addr0 (bigD1 ((p^-1)%g ord0)) //= -Hfg0 permKV eqxx eqd_mull //.
  rewrite -[X in _ %= X]mul1r eqd_mul ?eqd1 ?unitrX ?unitrN ?unitr1 //.
  rewrite (eq_bigl (fun i => (p^-1)%g ord0 != i)) ?big_lift_ord /=; last first.
    by move=> i /=; rewrite eq_sym.  
  exact: (IHj _ _ Hf2 Hg2 Hfg2).
rewrite !mxE /= (inj_eq (@ord_inj _)) -Hfg0 (inj_eq Hg) permKV.
by rewrite (negbTE (neq_lift _ _)) mul0r.
Qed.

Lemma prod_minor_seq : 
  \prod_(i < k) s`_i  = 
   minor [ffun x : 'I_k => widen_minl (widen_ord Hk x)]
   [ffun x : 'I_k => widen_minr (widen_ord Hk x)] (diag_mx_seq m n s). 
Proof.
rewrite /minor /submatrix.
elim: k Hk=>[H|j /= IHj Hj]; first by rewrite det_mx00 big_ord0.
have IH:= (ltnW Hj). 
apply: esym; rewrite (expand_det_row _ ord_max) big_ord_recr /= big1 ?add0r.
  rewrite /cofactor  /col' /row' !mxE !ffunE !matrix_comp.
  rewrite eqxx exprD -expr2 sqrr_sign mul1r.
  set M := matrix_of_fun _ _.
  have ->: M = 
         (\matrix_(i, j) (diag_mx_seq m n s)
                           ([ffun x => widen_minl (widen_ord IH x)] i)
                           ([ffun x => widen_minr (widen_ord IH x)] j)).
    apply/matrixP=> i l; rewrite !mxE !ffunE.
    have Hr: forall p, widen_ord Hj (lift ord_max p) = widen_ord IH p.
      by move=> p; apply: ord_inj=> /=; rewrite /bump leqNgt (ltn_ord p) add0n.
    by rewrite !Hr.    
  by rewrite -(IHj IH) big_ord_recr /= mulrC.
move=> i _; rewrite !mxE !ffunE /=.
by rewrite eqn_leq leqNgt (ltn_ord i) andFb mul0r.
Qed.

Lemma minor_eq0l (R : comRingType) k1 m1 n1  (s1 : seq R) x :
  forall (f : 'I_k1 -> 'I_m1) g, (n1 <= f x)%N ->
  minor f g (diag_mx_seq m1 n1 s1) = 0.
Proof.
move=> f g H.
rewrite /minor (expand_det_row _ x) big1 // => i _.
by rewrite !mxE gtn_eqF ?mul0r // (leq_trans _ H).
Qed.

Lemma minor_eq0r (R : comRingType) k1 m1 n1  (s1 : seq R) x :
  forall f (g : 'I_k1 -> 'I_n1) , (m1 <= g x)%N ->
  minor f g (diag_mx_seq m1 n1 s1) = 0.
Proof.
move=> f g H.
rewrite /minor (expand_det_col _ x) big1 // => i _.
by rewrite !mxE ltn_eqF ?mul0r // (leq_trans _ H).
Qed.

Lemma eqd_seq_gcdr : 
  \prod_(i < k) s`_i %= 
  \big[(@gcdr E)/0]_(f : {ffun 'I_k -> 'I_m}) 
  (\big[(@gcdr E)/0]_(g : {ffun 'I_k -> 'I_n}) minor f g (diag_mx_seq m n s)).
Proof.
apply/andP; split; last first.
  rewrite prod_minor_seq; set j := [ffun _ => _].
  by apply/(dvdr_trans (big_dvdr_gcdr _ j))/big_dvdr_gcdr. 
apply: big_gcdrP=> f; apply: big_gcdrP=> g.
case: (injectiveb f) /injectiveP=> Hinjf; last first.
  by rewrite (minor_f_not_injective _ _ Hinjf) dvdr0.
case: (injectiveb g) /injectiveP=> Hinjg; last first.
  by rewrite (minor_g_not_injective _ _ Hinjg) dvdr0.   
have Hmin k1 i m1 n1 (h : 'I_k1 -> 'I_m1) : (minn m1 n1 <= h i -> n1 <= h i)%N.
  move=> Hhi; have := (leq_ltn_trans Hhi (ltn_ord (h i))).
  by rewrite gtn_min ltnn=> /ltnW/minn_idPr <-.
case: (altP (@forallP _ (fun i => f i < minn m n)%N))=>[Hwf|]; last first.
  rewrite negb_forall=> /existsP [x]; rewrite -leqNgt=> /Hmin Hx.
  by rewrite (minor_eq0l _ _ Hx) dvdr0.
case: (altP (@forallP _ (fun i => g i < minn m n)%N))=>[Hwg|]; last first.
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
  rewrite [\sum_(_ <_) _](big1 _ xpredT) ?dvdr0 // => j _.
  rewrite !mxE -[(g j : nat)]/(g1 j : nat) -[(f y : nat)]/(f1 y : nat).
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
elim: k =>[?|j /= IHj g Hg]; first by rewrite big_ord0 dvd1r.
rewrite big_ord_recr /=.
pose max:= \max_i (g i).    
have [l Hl]: {j | max = g j} by apply: eq_bigmax; rewrite card_ord.
pose p := tperm l ord_max.  
set B := \prod_(_ < _) _.  
rewrite (reindex_inj (@perm_inj _ p)) /= big_ord_recr /= dvdr_mul //.
  pose f :=  (g \o p \o (widen_ord (leqnSn j))).    
  have Hf: injective f.
    apply: inj_comp=> [|x y /eqP].
      by apply: inj_comp=> //; exact: perm_inj. 
    by rewrite -(inj_eq (@ord_inj _)) /= => H; apply/ord_inj/eqP.
  have Hi: injective [ffun x => f x].     
    by move=> x e; rewrite !ffunE; exact: Hf.
  set C := \prod_(_ < _) _.
  have:= (IHj _ Hi).  
  have ->: C = \prod_i s`_([ffun x => f x] i).   
    by apply: eq_bigr=> i _; rewrite ffunE.   
  by apply.
have jleg : (j <= g (p ord_max))%N.
  rewrite /= tpermR; case/orP: (leq_total j (g l))=> //.
  rewrite leq_eqVlt; case/orP=> [|Hgm]; first by move/eqP=> ->; rewrite leqnn.
  have Habs: forall i, (g i < j)%N.
    move=> i; apply: (leq_ltn_trans _ Hgm).
    by rewrite -Hl /k; exact: (leq_bigmax i).
  pose f := fun x => Ordinal (Habs x).
  have Hf: injective f.
    move=> x y /eqP; rewrite -(inj_eq (@ord_inj _)) /= => /eqP Hxy.
    by apply/Hg/ord_inj.
  have: (#|'I_j.+1| <= #|'I_j|)%N.
    by rewrite -(card_codom Hf); exact: max_card.
  by rewrite !card_ord ltnn.
have [glts | ] := boolP (g (p ord_max) < size s)%N; last first.
  by rewrite -leqNgt => it; rewrite (nth_default 0 it) dvdr0.
apply: sorted_leq_nth.
 + exact: dvdr_trans.
 + exact: dvdrr.
 + exact: Hs.
 + by rewrite inE (leq_ltn_trans _ glts).
 + by rewrite inE.
 + by [].
Qed.

Lemma Smith_gcdr_spec : 
  \prod_(i < k) s`_i  %= 
  \big[(@gcdr E)/0]_(f : {ffun 'I_k -> 'I_m}) 
   (\big[(@gcdr E)/0]_(g : {ffun 'I_k -> 'I_n}) minor f g A) .
Proof.
rewrite (eqd_ltrans eqd_seq_gcdr).
have [ _ _ [M [N [_ _ Heqs]]]]:= HAs.
have [ _ _ [P [Q [_ _ Hseq]]]]:= (equiv_sym HAs).
rewrite conform_mx_id in Heqs.
rewrite conform_mx_id in Hseq.
have HdivmA p q k1 (B C : 'M[E]_(p,q)) (M1 : 'M_p) (N1 : 'M_q) :
   forall (H : M1 *m C *m N1 = B),
   forall (f : 'I_k1 -> 'I_p) (g : 'I_k1 -> 'I_q),
   \big[(@gcdr E)/0]_(f0 : {ffun 'I_k1 -> _}) 
    \big[(@gcdr E)/0]_(g0 : {ffun 'I_k1 -> _}) minor f0 g0 C
    %| minor f g B.
  move=> H f g. 
  have HBC: minor f g B =  \sum_(f0 : {ffun _ -> _ } | strictf f0)
                 ((\sum_(g0 : {ffun _ -> _ } | strictf g0)
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

Import GRing.Theory.
Import PolyPriField.
Variable E : euclidDomainType.

Lemma Smith_unicity n (A : 'M[E]_n) (s : seq E) :
  sorted %|%R s -> equivalent A (diag_mx_seq n n s) ->
  forall i, (i < n)%N -> s`_i %= (Smith_seq A)`_i.
Proof.
move=> Hs HAs i. 
have Hsmt := sorted_Smith A.
have HAsmt := equiv_Smith A.
elim: i {-2}i (leqnn i)=>[i|i IHi j Hji].
  rewrite leqn0 -[X in (i < X)%N]minnn=> /eqP -> Hi.
  have:= (Smith_gcdr_spec Hi Hs HAs).
  have:= (Smith_gcdr_spec Hi Hsmt HAsmt).
  rewrite !big_ord_recl !big_ord0 !mulr1 eqd_sym => H1 H2.
  exact: (eqd_trans H2 H1).
rewrite -[X in (j < X)%N]minnn=> Hj.
have:= (Smith_gcdr_spec Hj Hs HAs).
have:= (Smith_gcdr_spec Hj Hsmt HAsmt).
rewrite !big_ord_recr /= eqd_sym => H1 H2.
have {H1 H2} H3:= (eqd_trans H2 H1).
have H1: \prod_(i < j) s`_i %= \prod_(i < j) (Smith_seq A)`_i.
  rewrite minnn in Hj.
  apply: eqd_big_mul=> k _; apply: IHi.
    exact: (leq_trans (ltn_ord k) Hji).
  exact: (ltn_trans _ Hj).
case: (altP (\prod_(i < j) s`_i =P 0))=> H0; last first.
  by rewrite -(eqd_mul2l _ _ H0) (eqd_rtrans (eqd_mulr _ H1)).
have/prodf_eq0 [k _ /eqP Hk]: (\prod_(i < j) (Smith_seq A)`_i == 0).
  by rewrite H0 eqd0r in H1.
case/eqP/prodf_eq0: H0 => l _ /eqP Hl.
have sj0 : s`_j == 0.
  have [ jlts | ] := boolP(j < size s)%N; last first.
    by rewrite -leqNgt => it; rewrite (nth_default 0 it).
  rewrite -dvd0r -{1}Hl.
  apply: sorted_leq_nth => //.
    + exact: dvdr_trans.
    + by rewrite inE (ltn_trans _ jlts) //; case: l.
    + by case: l {Hl}=> l llt /=; rewrite ltnW.
have smsj0 : (Smith_seq A)`_j == 0.
  have [ jlts | ] := boolP(j < size (Smith_seq A))%N; last first.
    by rewrite -leqNgt => it; rewrite (nth_default 0 it).
  rewrite -dvd0r -{1}Hk.
  apply: sorted_leq_nth => //.
    + exact: dvdr_trans.
    + by rewrite inE (ltn_trans _ jlts) //; case: l.
    + by case: l {Hl}=> l llt /=; rewrite ltnW.
by rewrite (eqP sj0) (eqP smsj0).
Qed.

End Unicity.

 
