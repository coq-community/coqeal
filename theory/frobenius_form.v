From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_fingroup.
From mathcomp Require Import all_real_closed.
From CoqEAL Require Import binetcauchy ssrcomplements mxstructure minor.
From CoqEAL Require Import smith dvdring polydvd.
From CoqEAL Require Import similar perm_eq_image companion closed_poly smith_complements.

(**  This file provides a theory of invariant factors. The main result
     proved here is the similarity between a matrix and its Frobenius
     normal form.

        Frobenius_seq M == The same as the sequence Smith_seq (XI - M) where
                           each polynomial has been divded by their
                           lead coefficient (Hence each polynomial is monic).
    invariant_factors M == The sequence of non-constant polynomials of
                           Frobenius_seq M.
       Frobenius_form M == The block diagonal matrix formed by the
                           companion matrices of the invariant factors of M.
    Frobenius_form_CF M == The block diagonal matrix defined over a closed
                           field formed by the companion matrices of
                           the linear factors of the invariant factors of M.

                                                                              *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Frobenius.

Variable F : fieldType.
Local Notation E := {poly F}.
Import GRing.Theory.
Import PolyPriField.
Local Open Scope ring_scope.

Definition Frobenius_seq n (A : 'M[F]_n) :=
  [seq (lead_coef p)^-1 *: p | p : E <- take n (Smith_seq (char_poly_mx A))].

Lemma sorted_Frobenius_seq n (A : 'M[F]_n) :
  sorted (@dvdp _) (Frobenius_seq A).
Proof.
case: n A=> // n A.
have Hp: forall (p : E), ((lead_coef p)^-1 *: p %= p)%P.
  move=> p; have [-> | p0] := eqVneq p 0; first by rewrite scaler0 eqpxx.
  apply/eqpP; exists ((lead_coef p),1).
    by rewrite oner_neq0 andbT lead_coef_eq0.
  rewrite scalerA mulrV ?scale1r //.
  by rewrite unitfE lead_coef_eq0.
suff : sorted (@dvdr _) (Frobenius_seq A).
  by apply: sorted_trans=> x y _ _; rewrite dvdr_dvdp=> ->.
have /mono_sorted it
  : {mono (fun p : {poly F} => (lead_coef p)^-1 *: p) : x y /
   x %| y}.
  by move=> x y; rewrite !dvdr_dvdp (eqp_dvdl _ (Hp x)) (eqp_dvdr _ (Hp y)).
rewrite it.
set s := Smith_seq _.
apply/(sorted_take (@dvdr_trans _))/sorted_Smith.
Qed.

Lemma size_Frobenius_seq n (A : 'M[F]_n) : size (Frobenius_seq A) = n.
Proof.
by rewrite size_map size_Smith_seq // -size_poly_eq0 size_char_poly.
Qed.

Lemma Frobenius_seq_char_poly n (A : 'M[F]_n) :
\prod_(p <- Frobenius_seq A) p = char_poly A.
Proof.
rewrite big_map scaler_prod prodfV.
have Hs m (B : 'M[F]_m): size (take m (Smith_seq (char_poly_mx B))) = m.
  by move: (size_Frobenius_seq B); rewrite size_map.
have Hp1: \prod_(i <- (take n (Smith_seq (char_poly_mx A)))) i = char_poly A.
  case: n A => [A| n A]; first by rewrite big_nil /char_poly det_mx00.
  rewrite -(det_diag_mx_seq (Hs _ A)).
  by rewrite diag_mx_seq_takel det_Smith.
have ->: \prod_(i <- (take n (Smith_seq (char_poly_mx A)))) lead_coef i = 1.
  rewrite lead_coef_prod Hp1.
  by apply/monicP/char_poly_monic.
by rewrite Hp1 invr1 scale1r.
Qed.

Lemma Frobenius_seq_neq0 n (A : 'M[F]_n) p :
   p \in Frobenius_seq A -> p != 0.
Proof.
have Hc := (Frobenius_seq_char_poly A).
have: char_poly A != 0.
  by rewrite -size_poly_eq0 size_char_poly.
rewrite -Hc (big_nth 0) big_mkord.
move/prodf_neq0=> H0 /(nthP 0) [i Hi] <-.
exact: (H0 (Ordinal Hi)).
Qed.

Lemma monic_Frobenius_seq n (A : 'M[F]_n) p:
 p \in Frobenius_seq A -> p \is monic.
Proof.
move=> Hp.
have := Frobenius_seq_neq0 Hp.
move: Hp; rewrite /Frobenius_seq=> /(nthP 0) []i.
rewrite size_map=> Hi; rewrite (nth_map 0) // => <-.
rewrite scaler_eq0 negb_or=> /andP [_ H0].
by apply: monic_leadVMp; rewrite unitfE lead_coef_eq0.
Qed.

Lemma equiv_Frobenius_seq n (A : 'M[F]_n) :
  equivalent (diag_mx_seq n n (Smith_seq (char_poly_mx A)))
     (diag_mx_seq n n (Frobenius_seq A)).
Proof.
rewrite -diag_mx_seq_takel.
apply: eqd_equiv=> // [|i]; first by rewrite size_map.
set s := take _ _.
case: (ltnP i (size s)) => Hi; last by rewrite !nth_default // size_map.
rewrite (nth_map 0) //; apply/eqdP.
exists ((lead_coef s`_i)^-1%:P).
  have Hin: (Frobenius_seq A)`_i \in Frobenius_seq A.
    by rewrite mem_nth // size_map.
  have:= Frobenius_seq_neq0 Hin.
  rewrite (nth_map 0) // scaler_eq0 negb_or=> /andP [Hl _].
  by rewrite rmorph_unit // unitfE.
by rewrite mul_polyC.
Qed.

Definition invariant_factors n (A : 'M[F]_n) :=
  filter (fun p : E => (1 < size p)%N) (Frobenius_seq A).

Lemma invariant_factor_neq0 n (A : 'M[F]_n) :
 forall p, p \in invariant_factors A -> p != 0.
Proof.
by move=> p; rewrite mem_filter; case/andP=> _; exact: Frobenius_seq_neq0.
Qed.

Lemma monic_invariant_factors n (A : 'M[F]_n) :
  forall p, p \in invariant_factors A -> p \is monic.
Proof.
by move=> p; rewrite mem_filter; case/andP=> _; apply: monic_Frobenius_seq.
Qed.

Section dvdp_monic.

Local Open Scope ring_scope.
Import GRing.Theory.
Import PolyPriField.
Variable T : fieldType.

Definition dvdpm (p q : {poly T}) :=
  (p \is monic) && (q \is monic) && (dvdp p q).

Lemma dvdpm_trans : transitive dvdpm.
Proof.
move=> p q r /andP [] /andP [] Hq Hp Hqp /andP [] /andP [] _ Hr Hpr.
apply/andP; split; first by apply/andP.
exact: (dvdp_trans Hqp).
Qed.

Lemma dvdpm_asym : antisymmetric dvdpm.
Proof.
move=> p q /andP [] /andP [] /andP [] Hp Hq Hpq /andP [] _ Hqp.
by apply/eqP; rewrite -eqp_monic // /eqp Hpq.
Qed.

Lemma dvd1pm (p : {poly T}) : p \is monic -> dvdpm 1 p.
Proof.
have H1:= (@monic1 T).
move=> Hp; apply/andP; split; first by apply/andP.
by rewrite dvd1p.
Qed.

End dvdp_monic.

Lemma Frobenius_seqE n (A : 'M[F]_n) : Frobenius_seq A =
  nseq (n - size (invariant_factors A)) 1 ++ invariant_factors A.
Proof.
set m := subn _ _.
have HfA:= (size_Frobenius_seq A).
have Hfrob: sorted (@dvdpm F) (Frobenius_seq A).
  have Hdvd: {in (Frobenius_seq A) &, forall p q, dvdp p q -> dvdpm p q}.
    move=> p q /= /monic_Frobenius_seq Hp /monic_Frobenius_seq Hq H.
    by rewrite /dvdpm Hp Hq H.
  by apply/(sorted_trans Hdvd)/sorted_Frobenius_seq.
have Hst: sorted (@dvdpm F) (nseq m 1 ++ invariant_factors A).
  apply: (@path_sorted _ _ 1); rewrite cat_path; apply/andP; split.
    apply/(pathP 0); rewrite size_nseq=> [][|i] Hi.
      by rewrite nth0 dvd1pm // nth_nseq Hi monic1.
    rewrite -nth_behead nth_nseq (ltn_trans (ltnSn i) Hi) dvd1pm //.
    by rewrite nth_nseq Hi monic1.
  rewrite path_min_sorted; [|apply/allP=>p Hp].
    by rewrite sorted_filter //;first exact: dvdpm_trans.
  rewrite -nth_last nth_nseq size_nseq.
  by case: (m.-1 < m)%N; rewrite dvd1pm //; apply: (monic_invariant_factors Hp).
apply: (sorted_eq (@dvdpm_trans F) (@dvdpm_asym F) Hfrob Hst).
pose a:= fun p : E => (size p <= 1)%N.
have HaC: {in (Frobenius_seq A), (fun p : E => (1 < size p)%N) =1 (predC a)}.
  by move=> p /=; rewrite -ltnNge.
have Hfi: (invariant_factors A) = filter (predC a) (Frobenius_seq A).
  by rewrite -(eq_in_filter HaC).
have Hm: m = size (filter a (Frobenius_seq A)).
  rewrite /m Hfi !size_filter.
  apply/eqP; rewrite -(eqn_add2r (count (predC a) (Frobenius_seq A))).
  by apply/eqP; rewrite subnK ?count_predC // -{2}HfA count_size.
have Hfn: nseq m 1 = filter a (Frobenius_seq A).
  apply: (@eq_from_nth _ 0)=> [|i]; first by rewrite size_nseq.
  rewrite size_nseq => Hi; rewrite nth_nseq Hi.
  have: (filter a (Frobenius_seq A))`_i \in (filter a (Frobenius_seq A)).
    by rewrite mem_nth // -Hm.
  rewrite mem_filter=> /andP [Ha1 Ha2].
  move: (monicP (monic_Frobenius_seq Ha2)).
  by rewrite (size1_polyC Ha1) lead_coefC => ->.
by rewrite perm_sym Hfn Hfi; apply/permPl/perm_filterC.
Qed.

Lemma invf_char_poly n (A : 'M[F]_n) :
\prod_(p <- invariant_factors A) p = char_poly A.
Proof.
rewrite -Frobenius_seq_char_poly Frobenius_seqE.
rewrite big_cat /= (big1_seq (nseq _ _)) ?mul1r // => i.
case/andP=> _ /(nthP 0) [j].
by rewrite size_nseq=> Hj; rewrite nth_nseq Hj=> ->.
Qed.

Lemma dvdp_invf_char_poly m (A : 'M[F]_m) (p : {poly F}) :
p \in (invariant_factors A) -> dvdp p (char_poly A).
Proof.
move=> Hp.
rewrite -invf_char_poly prod_seq_count.
have Hi: p \in undup (invariant_factors A) by rewrite mem_undup.
rewrite (bigD1_seq _ Hi) ?undup_uniq //= dvdp_mulr // dvdp_exp //.
by rewrite -has_count has_pred1.
Qed.

Lemma sorted_invf n (A : 'M[F]_n) : sorted (@dvdp _) (invariant_factors A).
Proof.
have := sorted_Frobenius_seq A.
rewrite Frobenius_seqE.
apply: subseq_sorted.
  exact: dvdp_trans.
exact: suffix_subseq.
Qed.

Lemma sum_size_inv_factors n (A : 'M[F]_n) :
  (\sum_(p <- invariant_factors A) (size p).-1 = n)%N.
Proof.
have {2}->: n = n.+1.-1 by [].
rewrite -(size_char_poly A) -invf_char_poly.
rewrite !(big_nth 0) !big_mkord size_prod=> [|i _]; last first.
  by apply: (@invariant_factor_neq0 _ A); rewrite mem_nth.
rewrite subSKn -sum1_card; apply/eqP.
set s := (\sum_(i in _) 1)%N.
rewrite -(eqn_add2r s) subnK.
  apply/eqP; rewrite -big_split /=; apply: eq_bigr=> i _.
  rewrite addn1 prednK // size_poly_gt0.
  by apply: (@invariant_factor_neq0 _ A); rewrite mem_nth.
apply: leq_sum=> i _; rewrite size_poly_gt0.
by apply: (@invariant_factor_neq0 _ A); rewrite mem_nth.
Qed.

Lemma nnil_inv_factors n (A : 'M_n.+1) : invariant_factors A != [::].
Proof.
apply: contraPneq (sum_size_inv_factors A) => ->.
by rewrite big_nil.
Qed.

Let Smith_block_cpmx  n (A : 'M[F]_n) :=
  let sp := invariant_factors A in
  let size := [seq (size p).-2 | p : E <- sp] in
  let blocks m i := diag_mx_seq m.+1 m.+1 (rcons (nseq m 1) sp`_i) in
  diag_block_mx size blocks.

Let Smith_seq_cpmx n (A : 'M[F]_n) :=
  let sp := invariant_factors A in
  let m := size_sum [seq (size p).-2 | p : E <- sp] in
  diag_mx_seq m.+1 m.+1 (Frobenius_seq A).

Lemma cast_inv n (A : 'M[F]_n.+1) :
  size (Frobenius_seq A) =
  (size_sum [seq (size p).-2 | p : E <- invariant_factors A]).+1.
Proof.
rewrite size_Frobenius_seq -{1}(sum_size_inv_factors A).
rewrite size_sum_big; last first.
  by rewrite -size_eq0 size_map size_eq0 nnil_inv_factors.
rewrite !big_map /=; apply: eq_big_seq=> i.
rewrite mem_filter=> /andP [Hi _].
by rewrite prednK // -subn1 subn_gt0.
Qed.

Lemma equiv_sbc_ssc n (A : 'M[F]_n) :
  equivalent (Smith_block_cpmx A) (Smith_seq_cpmx A).
Proof.
rewrite /Smith_block_cpmx /Smith_seq_cpmx Frobenius_seqE.
have: forall p, p \in invariant_factors A -> (0 < (size p).-1)%N.
  by move=> p; rewrite mem_filter -subn1 subn_gt0=> /andP [].
rewrite -{10}(sum_size_inv_factors A).
case: (invariant_factors A)=> [_|a l].
  by rewrite big_nil diag_mx_seq_nil; exact: equiv_refl.
elim: l a=> /= [a Hp|b l IHl a Hp].
  by rewrite big_cons big_nil addn0 subn1 cats1; exact: equiv_refl.
have IHp : forall p : E, p \in b :: l -> (0 < (size p).-1)%N.
  by move=> p H; apply: Hp; rewrite mem_behead.
have Ha: (0 < (size a).-1)%N by  rewrite Hp // mem_head.
have Hb: (0 < (size b).-1)%N by rewrite IHp // mem_head.
set M := diag_mx_seq _ _ _.
apply: (equiv_trans (equiv_drblockmx M (IHl b IHp))).
rewrite -diag_mx_seq_cat ?size_rcons ?size_nseq //.
set s2 := [seq (size p).-2 | p : E <- (b :: l)].
set k := (\sum_(_ <- _) _)%N.
set m := (\sum_(_ <- _) _)%N.
have Hk: k = (size_sum s2).+1.
  rewrite size_sum_big_cons /k !big_cons !big_map /= prednK //.
  congr (_ + _)%N; apply: eq_big_seq=> i Hi.
  by rewrite (@prednK (size i).-1) // IHp // mem_behead.
have Hltk : (size l < k)%N.
  rewrite /k (eq_big_seq (fun p : E => (size p).-2 + 1)%N).
  rewrite big_split /= addnC (big_nth 0) sum_nat_const_nat.
    by rewrite subn0 muln1 leq_addr.
  by move=> i Hi /=; rewrite addn1 prednK // IHp.
apply/similar_equiv/similar_diag_mx_seq=> //.
  by rewrite !size_cat size_rcons !size_nseq subnK // Hk.
apply/seq.permP=> x /=.
rewrite -cats1 !count_cat /= !count_nseq.
rewrite !addnA addn0 (addnAC _ (x a)) -mulnDr; congr (_ * _ + _ + _ + _)%N.
by rewrite /m big_cons (subnS _ (size l).+1) -{2}(prednK Ha) -addnBA //.
Qed.

Lemma Smith_companion (p : E) : (1 < size p)%N -> p \is monic ->
  equivalent (Smith_form (char_poly_mx (companion_mx p)))
  (diag_mx_seq (size p).-2.+1 (size p).-2.+1 (rcons (nseq (size p).-2 1) p)).
Proof.
move=> Hsp Hmp.
rewrite /Smith_form -diag_mx_seq_takel.
set s := take _ _.
have Hs1: (size p).-2.+1 = size s.
  by rewrite -(size_Frobenius_seq (companion_mx p)) size_map.
have Hs2: (size p).-2.+1 = size (rcons (nseq (size p).-2 1) p).
  by rewrite size_rcons size_nseq.
apply: eqd_equiv=> //; first by rewrite -Hs1 -Hs2.
have := leqnSn (size p).-2.
rewrite -[X in (_ <= X)%N]minnn=> Hop.
have Hsort: sorted %|%R s.
  by apply/(sorted_take (@dvdr_trans _))/sorted_Smith.
have := (equiv_Smith (char_poly_mx (companion_mx p))).
rewrite /Smith_form -diag_mx_seq_takel=> Hsm.
have {Hop Hsort Hsm} := (Smith_gcdr_spec Hop Hsort Hsm).
set d := \big[_/_]_(_<_) _=> H.
have {H} Hd1: d %= 1.
  apply/(eqd_trans H)/andP; split; last by rewrite dvd1r.
  apply: big_gcdr_def; exists (finfun (lift ord0)).
  apply: big_gcdr_def; exists (finfun (lift ord_max)).
  rewrite /minor.minor /minor.submatrix /=.
  set M := \matrix_(_,_) _.
  have Hut: upper_triangular_mx M.
    apply/upper_triangular_mxP => i j Hij.
    rewrite !mxE !ffunE -(inj_eq (@ord_inj _)) lift0 lift_max.
    rewrite !eqn_leq !(leqNgt _ j) ltn_ord subr0.
    by rewrite ltnW // ltnNge Hij !andFb subr0.
  rewrite (det_triangular_mx Hut).
  rewrite (eq_bigr (fun _ => -1)) ?prodr_const ?card_ord; last first.
    move=> i; rewrite !mxE !ffunE -(inj_eq (@ord_inj _)) lift0 lift_max.
    by rewrite eqxx !eqn_leq ltnn (leqNgt _ i) ltn_ord sub0r subr0.
  by apply/dvdrP; exists ((-1)^+ (size p).-2); rewrite -expr2 sqrr_sign.
have Hip: s`_(size p).-2 %= p.
  rewrite eqd_sym in Hd1.
  rewrite -(mul1r s`_(size p).-2) (eqd_ltrans (eqd_mulr _ Hd1)).
   rewrite -{2}(comp_char_polyK Hmp Hsp) /char_poly -det_Smith.
  rewrite /Smith_form -diag_mx_seq_takel.
  rewrite det_diag_mx_seq // eqd_sym (big_nth 0) big_mkord.
  by rewrite -Hs1 big_ord_recr /=.
move/eqd_big_mul1: Hd1 => H i.
case: (ltngtP i (size p).-2) => Hi.
- by rewrite nth_rcons size_nseq Hi nth_nseq Hi (H (Ordinal Hi)).
- by rewrite !nth_default // -?Hs1 // size_rcons size_nseq.
by rewrite nth_rcons size_nseq Hi eqxx ltnn.
Qed.

Definition Frobenius_form n (A : 'M[F]_n) :=
  let sp := invariant_factors A in
  let size := [seq (size p).-2 | p : E <- sp] in
  let blocks n i := [seq companion_mxn n.+1 p | p <- sp]`_i in
   diag_block_mx size blocks.

Lemma Frobenius n (A : 'M[F]_n.+1) :
  similar A (Frobenius_form A).
Proof.
apply/similar_fundamental; rewrite char_diag_block_mx; last first.
  by rewrite -size_eq0 size_map size_eq0 nnil_inv_factors.
apply: (equiv_trans (equiv_Smith (char_poly_mx A))).
rewrite /Smith_form.
apply/(equiv_trans (equiv_Frobenius_seq A))/equiv_sym.
have Hn := size_Frobenius_seq A.
rewrite /equivalent -{2 4 37 38 43 44}Hn cast_inv.
apply: (equiv_trans _ (equiv_sbc_ssc A)).
apply: equiv_diag_block=>[|i]; first by rewrite !size_map.
rewrite size_map=> Hi.
rewrite !(nth_map 0) //.
set C := char_poly_mx _.
apply: (equiv_trans (equiv_Smith C)).
apply: Smith_companion; move: (mem_nth 0 Hi).
  by rewrite mem_filter=> /andP [].
exact: monic_invariant_factors.
Qed.

Lemma Frobenius_unicity n m (A : 'M[F]_n) (B : 'M_m) : similar A B <->
  invariant_factors A = invariant_factors B.
Proof.
split=> [[Hmn H]|H]; rewrite /invariant_factors.
  congr filter; apply: (@eq_from_nth _ 0)=>[|i Hi].
    by rewrite !size_Frobenius_seq.
  have/Frobenius_seq_neq0 := mem_nth 0 Hi.
  rewrite size_Frobenius_seq in Hi.
  rewrite !(nth_map 0) ?size_Smith_seq -?Hmn -?size_poly_eq0 ?size_char_poly //.
  rewrite size_poly_eq0 scaler_eq0 negb_or invr_eq0=> /andP [Hl0 _].
  apply: (scalerI Hl0); rewrite !scalerA mulrV ?unitfE // scale1r.
  apply: eqpfP; rewrite /eqp -!dvdr_dvdp [X in take X]Hmn.
  rewrite Hmn in Hi; rewrite !nth_take //.
  apply: Smith_unicity => //; first exact: sorted_Smith.
  set D := char_poly_mx A.
  rewrite -{3 4 6 7}Hmn.
  apply: (equiv_trans _ (equiv_Smith D)).
  by apply/similar_fundamental/similar_sym.
have/eqP: n = m.
- by rewrite -(sum_size_inv_factors A) -(sum_size_inv_factors B) H.
case: n A H => [A|n A]; case: m B=> [B|m B] H Hmn //.
  exact: similar0.
apply/(similar_trans (Frobenius A))/similar_sym/(similar_trans (Frobenius B)).
rewrite /Frobenius_form H.
exact: similar_refl.
Qed.

Lemma mxminpoly_inv_factors n (A : 'M[F]_n.+1) :
  last 0 (Frobenius_seq A) = mxminpoly A.
Proof.
have Hif: (0 < size (invariant_factors A))%N.
  by rewrite lt0n size_eq0 nnil_inv_factors.
have Hfn: [seq (size p).-2 | p : E <- invariant_factors A] != [::].
  by rewrite -size_eq0 size_map size_eq0 nnil_inv_factors.
apply: mxminpolyP=> [||q HA].
- apply: (@monic_Frobenius_seq _ A).
  by rewrite -nth_last mem_nth // size_Frobenius_seq.
- apply: (similar_horner (similar_sym (Frobenius A))).
  rewrite horner_mx_diag_block //.
  apply/diag_block_mx0=> i; rewrite size_map=> Hi.
  rewrite !(nth_map 0) // Frobenius_seqE last_cat -nth_last.
  rewrite (set_nth_default 0) ?prednK // ?Hif //.
  set p := nth _ _ _.
  apply: (@horner_mx_dvdp _ _ p).
    apply: sorted_leq_nth=> //.
    - exact: dvdp_trans.
    - exact: sorted_invf.
    - by rewrite inE prednK.
    by rewrite -ltnS prednK.
  rewrite -{5}[p]comp_mxminpolyK.
  - exact: mx_root_minpoly.
  - exact: (monic_invariant_factors (mem_nth 0 Hi)).
  move: (mem_nth 0 Hi).
  by rewrite mem_filter -subn_gt0 subn1; case/andP.
move: (similar_horner (Frobenius A) HA).
rewrite horner_mx_diag_block // => /diag_block_mx0=> H.
rewrite Frobenius_seqE last_cat -nth_last (set_nth_default 0) ?prednK //.
move: (H (size (invariant_factors A)).-1).
rewrite size_map !(nth_map 0) ?prednK //.
set p := nth _ _ _=> Hp.
have Hm:= @mem_nth _ 0 (invariant_factors A) (size (invariant_factors A)).-1.
rewrite -[p]comp_mxminpolyK ?dvdr_dvdp.
- exact: (mxminpoly_min (Hp (leqnn _))).
- apply/(@monic_invariant_factors _ A)/Hm.
  by rewrite prednK // mem_filter -subn_gt0 subn1.
move: Hm; rewrite prednK // mem_filter -subn_gt0 subn1=> h.
by case/andP: (h (leqnn _)).
Qed.

End Frobenius.

Section Polynomial.

Local Open Scope ring_scope.
Import GRing.Theory.
Import PolyPriField.

Variable R : closedFieldType.

Lemma similar_poly_inv (p : {poly R}) :
  let sp := linear_factor_seq p in
  let size_seq := [seq (size p).-2 | p : {poly R} <- sp] in
  let blocks n i := companion_mxn n.+1 sp`_i in
  (1 < (size p))%N ->  p \is monic ->
  similar (companion_mx p) (diag_block_mx size_seq blocks).
Proof.
move=> /= Hp1 Hmp.
move: (@coprimep_linear_factor_seq _ p).
move: (@monic_linear_factor_seq _ p).
move: (@size_linear_factor_leq1 _ p).
move: Hmp Hp1 (monic_prod_factor Hmp).
elim: (linear_factor_seq p) {1 2 3 14 16}p.
  move=> p0 Hmp0 Hsp0; rewrite big_nil=> H.
  by rewrite H size_poly1 in Hsp0.
move=> a; case=> [_ p1 _ _ Hp1 _ _ _ | b l IHl p1 Hmp1 Hsp1 Hp1 Hs Hm Hcp] /=.
  rewrite Hp1 big_cons big_nil mulr1.
  by apply: similar_refl.
have Hicp : forall i j : 'I_(size (b :: l)), i != j ->
    coprimep (b :: l)`_i (b :: l)`_j.
  move=> i j H.
  have Hij: (lift ord0 i) != (lift ord0 j).
    by apply/val_eqP=> /lift_inj; apply/eqP.
  by move: (Hcp _ _ Hij); rewrite -!nth_behead.
pose p2:= p1 %/ a.
have Hma: a \is monic by apply: Hm; rewrite mem_head.
have Hsa: (1 < size a)%N by apply: Hs; rewrite mem_head.
have Hp2: p2 = \prod_(x <- (b :: l)) x.
  by rewrite /p2 Hp1 big_cons divr_mulKr // monic_neq0.
have Hml: forall x, x \in (b :: l) -> x \is monic.
  by move=> x Hx; apply: Hm; rewrite mem_behead.
have Hsl: forall x, x \in b :: l -> (1 < size x)%N.
  by move=> x Hx; apply: Hs; rewrite mem_behead.
have {Hs} Hsb: (1 < size b)%N by apply: Hsl; rewrite mem_head.
have {Hm} Hmb: b \is monic by apply: Hml; rewrite mem_head.
have {Hp1} Hp12: p1 = a * p2 by rewrite Hp1 Hp2 big_cons.
have Hmp2: p2 \is monic by rewrite -(monicMl _ Hma) -Hp12.
have sp1gt0 : (0 < size (1%:P : {poly R}))%N by rewrite size_poly1.
have mgt0 (x y : {poly R}) :
        (0 < size x -> 0 < size y -> 0 < size (x * y)%R)%N.
  by move=> sx sy; rewrite size_mul -?size_poly_eq0; move: sx sy;
        case: (size x); case: (size y) => // n1 n2; rewrite ?addnS.
have {Hsb Hmb} Hsp2: (1 < size p2)%N.
  rewrite Hp2 big_cons size_proper_mul.
    rewrite -subn1 -addnBA ?ltn_addr //.
    rewrite big_seq.
    apply: (big_ind (fun (p : {poly R}) => (0 < size p)%N) sp1gt0 mgt0)=> q Hq.
    have: (1 < size q)%N by apply: Hsl; rewrite mem_behead.
    by apply: ltn_trans.
  move/monicP: Hmb => ->; rewrite mul1r lead_coef_eq0 -size_poly_leq0.
  rewrite -ltnNge big_seq.
  apply: (big_ind (fun (p : {poly R}) => (0 < size p)%N) sp1gt0 mgt0)=> q Hq.
  have: (1 < size q)%N by apply: Hsl; rewrite mem_behead.
  by apply: ltn_trans.
move=> {sp1gt0 mgt0}.
apply: (@similar_trans _ _ _ _
           (block_mx (companion_mx a) 0 0 (companion_mx p2))); last first.
  by apply: (similar_drblockmx _ (IHl _ Hmp2 Hsp2 Hp2 Hsl Hml Hicp)).
have {Hp2 Hml Hsl Hcp Hicp IHl} Hcap: coprimep a p2.
  have copa1 : coprimep a 1%P by apply: coprimep1.
  have copaxy (x y : {poly R}) : coprimep a x -> coprimep a y ->
                   coprimep a (x * y)%R.
    by rewrite coprimepMr=> -> ->.
  rewrite Hp2 big_seq.
  apply: (big_ind (fun p => coprimep a p)).
   + by apply: coprimep1.
   + by move=> x y; rewrite coprimepMr => -> ->.
   move=> i iin; move/(nth_index 0): (iin)=> iid.
   move: (iin); rewrite -index_mem -ltnS=> ii_prf.
   set j := Ordinal ii_prf.
   have vi : [:: a, b & l]`_j = i by apply: (nth_index 0 iin).
   by have := Hcp ord0 j isT; rewrite vi /=.
apply/similar_fundamental.
apply: (equiv_trans (equiv_Smith _)).
apply: (equiv_trans (Smith_companion Hsp1 Hmp1)).
rewrite Hp12 char_dblock_mx.
apply: (@equiv_trans _ _ _ _ _ _ _
  (block_mx (diag_mx_seq (size a).-2.+1 (size a).-2.+1
  (rcons (nseq (size a).-2 1) a)) 0 0
  (diag_mx_seq (size p2).-2.+1 (size p2).-2.+1
  (rcons (nseq (size p2).-2 1) p2)))); last first.
  apply: equiv_dgblockmx; apply: equiv_sym; set C := char_poly_mx _ .
    by apply: (equiv_trans (equiv_Smith C)); apply: Smith_companion.
  by apply: (equiv_trans (equiv_Smith C)); apply: Smith_companion.
rewrite -diag_mx_seq_cat ?size_rcons ?size_nseq //.
set M := diag_mx_seq _ _ (_ ++ _).
set sap := (size (a * p2)).-2.+1.
set sa := (size a).-2.+1.
set sp := (size p2).-2.+1.
have Hcast: sap = (sa + sp)%N.
  rewrite /sap /sa /sp size_proper_mul.
    rewrite -!subn1 -addnBA; last by rewrite ltnW.
    rewrite addnC -addnBA; last by rewrite ltnW.
    rewrite -addnBA ?subn_gt0 // addSn addnC !subn1 (@prednK (_.-1)) //.
    by rewrite -subn1 subn_gt0.
  by move/monicP: Hma; move/monicP: Hmp2=> -> ->; rewrite mulr1 oner_eq0.
have HdetM: \det M = p1.
  rewrite det_diag_mx_seq ?size_cat ?size_rcons ?size_nseq //.
  rewrite -!cats1 !big_cat /= !big_cons !big_nil.
  rewrite !big1_seq=> [|i|i]; try by rewrite mem_nseq => /= /andP[] _ /eqP.
  by rewrite !mul1r !mulr1 -Hp12.
have Ho: (sa.-1 < (sa + sp).-1)%N by rewrite prednK // addnS leq_addr.
have HM1: row' (Ordinal Ho) (col' (Ordinal Ho)
            (row' ord_max (col' ord_max  M))) = 1%:M.
  apply/matrixP=> j k; rewrite !mxE !lift_max.
  rewrite nth_cat size_rcons size_nseq.
  case: ifP; rewrite nth_rcons size_nseq.
    rewrite ltnS leq_eqVlt eq_sym (negbTE (neq_bump _ _)) /= => Hb.
    by rewrite Hb nth_nseq Hb eqn_leq !leq_bump2 -eqn_leq.
  move/negbT;rewrite -leqNgt=> Hb.
  have Hb2: (bump (size a).-2 j - (size a).-2.+1 < (size p2).-2)%N.
    rewrite -(ltn_add2r sa _ _.-2) subnK //.
    by rewrite (leq_trans (ltn_ord (lift (Ordinal Ho) j))) // addnC addSn.
  by rewrite Hb2 nth_nseq Hb2 eqn_leq !leq_bump2 -eqn_leq.
apply/equiv_sym/(equiv_trans (equiv_Smith M)).
rewrite /Smith_form -diag_mx_seq_takel.
set s := take _ _.
have Hs1: size s = sap by rewrite Hcast size_Smith_seq // HdetM monic_neq0.
apply: eqd_equiv=> // [|i]; first by rewrite size_rcons size_nseq.
have Hle: (sap.-2 <= sa + sp)%N by rewrite -Hcast -subn2 leq_subr.
have Hsort: sorted (@dvdr _) s.
  by apply/(sorted_take (@dvdr_trans _))/sorted_Smith.
have:= (equiv_Smith M).
rewrite /Smith_form -diag_mx_seq_takel=> Hequiv.
have Hle2: (sap.-2 < minn (sa + sp) (sa + sp))%N
   by rewrite minnn Hcast addnS addSn.
have:= Smith_gcdr_spec Hle2 Hsort Hequiv.
set d2 := \big[_/_]_(_<_) _=> H2.
have {H2} Hd2: d2 %= 1.
  apply/(eqd_trans H2); rewrite /eqd !dvdr_dvdp.
  apply: (coprimepP _ _ Hcap); rewrite -dvdr_dvdp.
  +apply: big_gcdr_def; rewrite Hcast prednK ?addnS ?addSn //.
   exists (finfun (lift (@ord_max (sa + sp).-1))).
   apply: big_gcdr_def.
   exists (finfun (lift (@ord_max (sa + sp).-1))).
   rewrite /minor.minor /minor.submatrix /=.
   rewrite (expand_det_row _ (Ordinal Ho)) (bigD1 (Ordinal Ho)) //=.
   rewrite !mxE !ffunE big1 ?addr0.
     rewrite nth_cat size_rcons size_nseq lift_max /=.
     rewrite ltnS leqnn nth_rcons size_nseq ltnn eqxx.
     rewrite /cofactor exprD -expr2 sqrr_sign mul1r.
     set N:= row' _ _.
     have ->: N = 1%:M.
     by rewrite -HM1; apply/matrixP=> j k; rewrite !mxE !ffunE !lift_max.
   by rewrite det1 mulr1.
   move=> j /negbTE Hj; rewrite !mxE !ffunE.
   by rewrite (inj_eq (@ord_inj _)) (inj_eq (@lift_inj _ _)) eq_sym Hj mul0r.
  have Ho2: (sa .-1 < sa + sp)%N by rewrite prednK // leq_addr.
  apply: big_gcdr_def; rewrite Hcast prednK ?addnS ?addSn //.
  exists (finfun (lift (Ordinal Ho2))).
  apply: big_gcdr_def.
  exists (finfun (lift (Ordinal Ho2))).
  rewrite /minor.minor /minor.submatrix /=.
  have Hom: ((size a).-2 + (size p2).-2 < (size a).-2 + sp)%N by rewrite addnS.
  have Hlom k : lift (Ordinal Hom) k = widen_ord (leq_pred _) k.
    apply: ord_inj=> /=; rewrite /bump leqNgt.
    by rewrite (leq_trans (ltn_ord k)) // addnS leqnn.
  rewrite (expand_det_row _ (Ordinal Hom)).
  rewrite (bigD1 (Ordinal Hom)) //= big1 ?addr0.
    rewrite !mxE !ffunE /= -[X in bump X _]addn0 bumpDl /bump leq0n /=.
    rewrite nth_cat size_rcons size_nseq ltnS add1n {1}addnS.
    rewrite ltnNge leq_addr /= nth_rcons size_nseq.
    rewrite {1 3}addnS !subSS !addKn !ltnn !eqxx.
    rewrite /cofactor exprD -expr2 sqrr_sign mul1r.
    set N:= row' _ _.
    have ->: N = 1%:M.
      rewrite -HM1; apply/matrixP=> j k.
      by rewrite !mxE !ffunE !lift_max !Hlom /=.
    by rewrite det1 mulr1.
  move=> j /negbTE Hj; rewrite !mxE !ffunE (inj_eq (@ord_inj _)).
  by rewrite (inj_eq (@lift_inj _ _)) eq_sym Hj mul0r.
have Hsp: s`_sap.-1 %= p1.
  rewrite eqd_sym in Hd2.
  rewrite -(mul1r s`_sap.-1) (eqd_ltrans (eqd_mulr _ Hd2)).
  rewrite -HdetM -det_Smith /Smith_form -diag_mx_seq_takel det_diag_mx_seq.
    rewrite (big_nth 0) big_mkord Hs1 big_ord_recr /=.
    by apply: eqd_mul=> //; rewrite /d2 prednK // Hcast addnS addSn.
  by rewrite Hs1 Hcast.
move/eqd_big_mul1: Hd2=> H.
have [Hi|Hi|/eqP Hi] := (ltngtP i sap.-1).
  +have Hi2: (i < sap.-2.+1)%N by rewrite prednK // Hcast addnS addSn.
   rewrite nth_rcons size_nseq Hi nth_nseq Hi.
   exact: (H (Ordinal Hi2)).
  by rewrite !nth_default // ?Hs1 // size_rcons size_nseq.
by rewrite nth_rcons size_nseq Hi (eqP Hi) ltnn -Hp12.
Qed.

Definition Frobenius_form_CF n (A : 'M[R]_n) :=
  let fm f s := flatten (map f s) in
  let sp := invariant_factors A in
  let l p := linear_factor_seq p in
  let sc p := [seq (size q).-2 | q : {poly R} <- l p] in
  let size := flatten (map sc sp) in
  let blocks m i :=  companion_mxn m.+1 (fm l sp)`_i in
   diag_block_mx size blocks.

Lemma similar_Frobenius n (A : 'M[R]_n.+1) :
 similar (Frobenius_form A) (Frobenius_form_CF A).
Proof.
rewrite /Frobenius_form /Frobenius_form_CF.
move: (@monic_invariant_factors _ _ A).
have: forall p, p \in (invariant_factors A) -> (1 < size p)%N.
  by move=> p; rewrite mem_filter; case/andP.
case: (invariant_factors A)=>[_ _|a l]; first exact: similar_refl.
elim: l a=> /= [a Hsa Hma |b l IHl a Hs Hm].
  rewrite !cats0; apply: similar_poly_inv.
    by rewrite Hsa // mem_head.
  by rewrite Hma // mem_head.
have IHs: forall p : {poly R}, p \in b :: l -> (1 < size p)%N.
  by move=> p Hp; apply: Hs; rewrite mem_behead.
have IHm: forall p : {poly R}, p \in b :: l -> p \is monic.
  by move=> p HP; apply: Hm; rewrite mem_behead.
have Hsa: (1 < size a)%N by rewrite Hs // mem_head.
have Hma: a \is monic by rewrite Hm // mem_head.
set M := companion_mxn _ _.
apply: (similar_trans (similar_drblockmx M (IHl b IHs IHm))).
apply: (similar_trans (similar_ulblockmx _ (similar_poly_inv Hsa Hma))).
have Hnv: forall p, p \in [:: a, b & l] -> linear_factor_seq p != [::].
  move=> p Hp; rewrite /linear_factor_seq -size_eq0 !size_map size_eq0.
  rewrite /root_seq_uniq; apply: contra_neq; first exact: undup_nil.
  by rewrite -root_seq_nil -ltnNge; apply: Hs.
set s1 := _ ++ _.
set s2 := linear_factor_seq _ ++ _.
have: (linear_factor_seq a) != [::] by rewrite Hnv // mem_head.
have t: s2 != [::].
  have: linear_factor_seq b != [::] by rewrite Hnv // mem_behead // mem_head.
  by rewrite /s2; case: (linear_factor_seq b).
clear -t.
have ->: s1 = [seq (size p).-2 | p : {poly R} <- s2].
  by rewrite /s1 map_cat map_flatten; congr (_ ++ _); rewrite [in LHS]map_comp.
case: (linear_factor_seq a)=> //= c s _.
elim: s c=> [c|c s IHs d] /=.
  case: s2 t => // d s2 _ /=.
  exact: similar_refl.
set M := companion_mxn _ _.
apply: similar_sym.
apply: (similar_trans (similar_drblockmx M (similar_sym (IHs c)))).
rewrite /GRing.zero /= -row_mx_const -col_mx_const block_mxA.
apply/similar_sym/similar_cast.
rewrite col_mx_const row_mx_const.
exact: similar_refl.
Qed.

End Polynomial.
