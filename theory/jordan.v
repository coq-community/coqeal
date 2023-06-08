From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_fingroup.
From mathcomp Require Import all_real_closed.
From CoqEAL Require Import binetcauchy ssrcomplements mxstructure minor.
From CoqEAL Require Import smith dvdring polydvd.
From CoqEAL Require Import similar perm_eq_image companion closed_poly smith_complements.
From CoqEAL Require Import frobenius_form.

(**  The main result of this file is the theorem of Jordan decomposition.
     A direct consequence of this theorem is the diagonalization theorem.

      Jordan_block lam n == The Jordan block of dimension n with
                            the value lam on the diagonal.
           Jordan_form M == The block diagonal matrix formed by the
                            Jordan blocks of roots of invariant
                            factors of M, and of dimension their
                            multiplicity.

                                                                              *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section def.

Variable R : ringType.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition Jordan_block lam n : 'M[R]_n :=
  \matrix_(i,j) (lam *+ (i == j :> nat) + (i.+1 == j)%:R).

Lemma Jordan_block0 : Jordan_block 0 1 = 0.
Proof.
by apply/matrixP=> i j; rewrite !mxE !ord1 addr0.
Qed.

Lemma upt_Jordan_block lam n : upper_triangular_mx (Jordan_block lam n).
Proof.
apply/upper_triangular_mxP=> i j Hij ; rewrite mxE.
by rewrite (gtn_eqF Hij) eqn_leq ltnNge (ltnW Hij) addr0.
Qed.

End def.


Section trigonal.

Variable R : comRingType.
Import GRing.Theory.
Local Open Scope ring_scope.


Lemma det_Jordan_block (lam : R) n : \det (Jordan_block lam n) = lam ^+ n.
Proof.
rewrite det_triangular_mx; last by apply: upt_Jordan_block.
rewrite -{8}[n]card_ord -prodr_const.
by apply: eq_bigr=> i _; rewrite mxE eqxx eqn_leq ltnn addr0.
Qed.

Lemma Jordan_expn (lam : R) n k :
  (Jordan_block lam n.+1)^+ k =
   \matrix_(i,j) (('C(k,j - i)%:R * (lam^+ (k - (j - i)))) *+ (i <= j)).
Proof.
elim: k =>[|k IHk].
  apply/matrixP=> i j; rewrite !mxE bin0n subn_eq0 sub0n mulr1 [RHS]mulrb.
  by rewrite -(inj_eq (@ord_inj _)) eqn_leq /andb; case: ifP.
rewrite exprS IHk.
apply/matrixP=> i j; rewrite !mxE.
case: (eqVneq i ord_max) => Hi.
- rewrite (bigD1 i) //= !mxE big1 ?addr0=>[|l /negbTE Hl].
  - rewrite eqxx eqn_leq ltnn addr0.
    have ->: (j - i)%N = 0%N by apply/eqP; rewrite subn_eq0 Hi -ltnS.
    by rewrite !bin0 !mul1r !subn0 mulrnAr exprS.
  rewrite !mxE eq_sym [(_ == _ :> nat)]Hl Hi eqn_leq.
  by rewrite ltnNge -ltnS ltn_ord addr0 mul0r.
have Ho: (i.+1 < n.+1)%N by rewrite ltn_neqAle Hi ltn_ord.
rewrite (bigD1 i) //= (bigD1 (Ordinal Ho)); last first.
  by rewrite -(inj_eq (@ord_inj _)) eqn_leq ltnn.
rewrite !mxE eqxx (@eq_sym nat i) !eqn_leq !ltnn addr0 add0r.
rewrite !leqnn mul1r subnS /= big1 ?addr0; last first.
  move=> l /andP [] /negbTE Hil /negbTE Hl.
  by rewrite !mxE eq_sym [_ == _ :>nat]Hil eq_sym [_ == _ :>nat]Hl addr0 mul0r.
case: (ltngtP i j)=> Hij; last first.
  (*******************cas i = j***********************************)
- by rewrite Hij subnn !subn0 addr0 !bin0 !mul1r exprS.
  (****************** cas j < i ****************************************)
- by rewrite addr0 mulr0.
(************* cas    i <= j***************************)
rewrite !mulr1n mulrC -mulrA -exprSr -{2}subn1.
have H1ij: (1 <= j - i)%N by rewrite subn_gt0.
rewrite (subnBA _  H1ij) addn1.
case: (leqP (j-i) k)=> Hijk.
  by rewrite (subSn Hijk) -mulrDl -{1}(prednK H1ij) -natrD -binS prednK.
have:= Hijk; rewrite -subn_eq0=> /eqP Hijk2.
rewrite (bin_small Hijk) // mul0r Hijk2 !mulr1 add0r.
rewrite leq_eqVlt in Hijk.
case/orP: Hijk=> Hijk.
  rewrite (eqP Hijk) binn.
  rewrite -(prednK H1ij) eqSS in Hijk.
  by rewrite (eqP Hijk) binn.
by rewrite !bin_small // -ltnS prednK.
Qed.


Lemma char_poly_Jordan_block (lam : R) n :
  char_poly (Jordan_block lam n) = ('X - lam%:P) ^+n.
Proof.
rewrite char_poly_triangular_mx; last by apply: upt_Jordan_block.
rewrite  (eq_bigr (fun _ => ('X - lam%:P))) ?prodr_const ?card_ord //.
by move=> i; rewrite mxE eqxx eqn_leq ltnn addr0.
Qed.

End trigonal.

Section similar.

Variable R : fieldType.
Import GRing.Theory.
Import PolyPriField.
Local Open Scope ring_scope.


Lemma similar_cj n (lam : R) :
  similar (companion_mx (('X - lam%:P)^+ n.+1)) (Jordan_block lam n.+1).
Proof.
set p := _^+n.+1.
have Hmp: p \is monic by rewrite monic_exp // monicXsubC.
have Hsp: (1 < size p)%N by rewrite size_exp_XsubC.
apply/similar_fundamental.
apply: (equiv_trans  (equiv_Smith _)).
apply: (equiv_trans (Smith_companion Hsp Hmp)).
set M := char_poly_mx _.
apply/equiv_sym/(equiv_trans (equiv_Smith M)).
rewrite /Smith_form -diag_mx_seq_takel.
set s := take _ _.
have Hs1: size s = n.+1.
  rewrite size_Smith_seq // -/(char_poly _) char_poly_Jordan_block.
  by rewrite -size_poly_eq0 size_exp_XsubC.
apply: eqd_equiv; rewrite ?size_exp_XsubC // ?size_rcons ?size_nseq //=.
have Hsort: sorted (@dvdr _) s.
  by apply/(sorted_take (@dvdr_trans _))/sorted_Smith.
move: (equiv_Smith M).
rewrite /Smith_form -diag_mx_seq_takel => Hequiv.
have Hlemin: (n <= minn n.+1 n.+1)%N by rewrite minnn.
move: (Smith_gcdr_spec Hlemin Hsort Hequiv).
set d := \big[_/_]_(_<_) _=> H.
have {H} Hd1: d %= 1.
  apply/(eqd_trans H)/andP; split; last by rewrite dvd1r.
  apply: big_gcdr_def; exists (finfun (lift ord_max)).
  apply: big_gcdr_def; exists (finfun (lift ord0)).
  rewrite /minor.minor /minor.submatrix /=.
  set N := \matrix_(_,_) _.
  have Hut: upper_triangular_mx N^T.
    apply/upper_triangular_mxP=> i j Hij.
    rewrite !mxE !ffunE -(inj_eq (@ord_inj _)) lift0 lift_max.
    rewrite !eqn_leq !(leqNgt _ j) ltnS (ltnW Hij) ltnNge Hij.
    by rewrite andbF addr0 subr0.
  rewrite -det_tr (det_triangular_mx Hut).
  rewrite (eq_bigr (fun _ => -1)) ?prodr_const ?card_ord; last first.
    move=> i; rewrite !mxE !ffunE -(inj_eq (@ord_inj _)) lift0 lift_max.
    by rewrite eqxx !eqn_leq ltnn andbF sub0r add0r.
  by apply/dvdrP; exists ((-1)^+ n); rewrite -expr2 sqrr_sign.
have Hip: s`_n %= p.
  rewrite eqd_sym in Hd1.
  rewrite -(mul1r s`_n) (eqd_ltrans (eqd_mulr _ Hd1)).
  rewrite /p -char_poly_Jordan_block /char_poly -det_Smith.
  rewrite /Smith_form -diag_mx_seq_takel det_diag_mx_seq //.
  by rewrite (big_nth 0) big_mkord Hs1 big_ord_recr.
move/eqd_big_mul1: Hd1 => H i.
case: (ltngtP i n) => Hi.
- by rewrite nth_rcons size_nseq Hi nth_nseq Hi (H (Ordinal Hi)).
- by rewrite !nth_default // ?Hs1 // size_rcons size_nseq.
by rewrite nth_rcons size_nseq Hi ltnn eqxx.
Qed.

End similar.


Section jordan.

Variable R : closedFieldType.
Import GRing.Theory.
Import PolyPriField.
Local Open Scope ring_scope.


Definition Jordan_form m (A : 'M[R]_m.+1) :=
  let sp := root_seq_poly (invariant_factors A) in
  let sizes := [seq (x.2).-1 | x <- sp] in
  let blocks n i := Jordan_block (nth (0,0%N) sp i).1 n.+1 in
   diag_block_mx sizes blocks.

Lemma upt_Jordan n (A : 'M[R]_n.+1) :
  upper_triangular_mx (Jordan_form A).
Proof.
apply: upper_triangular_diag_block=> j.
exact: upt_Jordan_block.
Qed.

Lemma Jordan n (A : 'M[R]_n.+1) : similar A (Jordan_form A).
Proof.
apply: (similar_trans (Frobenius _)).
apply: (similar_trans (similar_Frobenius _)).
rewrite /Frobenius_form_CF /Jordan_form /root_seq_poly /linear_factor_seq.
set s1 := flatten _.
set s2 := map _ _.
have Hs: size s1 = size s2.
  rewrite /s1 size_map.
  by do 2! rewrite map_comp -map_flatten size_map.
apply: similar_diag_block=> // i; rewrite /s1.
(do 2! rewrite map_comp -map_flatten size_map) => Hi.
rewrite !(nth_map 0) ?size_map //.
rewrite !(nth_map (0,0%N)) ?size_map //.
set x := nth _ _ _.
rewrite -(@prednK x.2); first exact: similar_cj.
have/flattenP [s Hfs Hx] := mem_nth (0,0%N) Hi; move: Hfs.
case/(nthP nil)=> m; rewrite !size_map=> Hm Heq.
move: Heq Hx; rewrite (nth_map 0) // => <-.
apply: root_mu_seq_pos.
apply: (@invariant_factor_neq0 _ _ A).
by rewrite mem_nth.
Qed.

Lemma Jordan_char_poly n (A : 'M_n.+1) :
  char_poly A = \prod_i ('X - ((Jordan_form A) i i)%:P).
Proof.
rewrite (similar_char_poly (Jordan A)).
exact: (char_poly_triangular_mx (upt_Jordan A)).
Qed.

Lemma eigen_diag n (A : 'M_n.+1) :
  let sp := root_seq_poly (invariant_factors A) in
  let sizes := [seq (x.2).-1 | x <- sp] in
  perm_eq [seq (Jordan_form A) i i | i <- enum 'I_(size_sum sizes).+1]
          (root_seq (char_poly A)).
Proof.
have Hinj: injective (fun (c : R) => 'X - c%:P).
  by move=> x y /= H; apply/polyC_inj/oppr_inj/(addrI 'X).
apply: (perm_map_inj Hinj).
apply: (@unicity_decomposition _ _ _ (char_poly A)).
+ move=> r /(nthP 0) []i; rewrite !size_map=> Hi.
  rewrite (nth_map 0) ?size_map // => <-.
  exact: irredp_XsubC.
- move=> r /(nthP 0) []i; rewrite !size_map=> Hi.
  rewrite (nth_map 0) ?size_map // => <-.
  exact: irredp_XsubC.
+ move=> r /(nthP 0) []i; rewrite !size_map=> Hi.
  rewrite (nth_map 0) ?size_map // => <-.
  exact: monicXsubC.
- move=> r /(nthP 0) []i; rewrite !size_map=> Hi.
  rewrite (nth_map 0) ?size_map // => <-.
  exact: monicXsubC.
+ by rewrite !big_map; exact: Jordan_char_poly.
rewrite big_map {1}[char_poly A]root_seq_eq.
by rewrite (monicP (char_poly_monic A)) scale1r.
Qed.

Lemma diagonalization n (A : 'M[R]_n.+1) : uniq (root_seq (mxminpoly A)) ->
  similar A (diag_mx_seq n.+1 n.+1 (root_seq (char_poly A))).
Proof.
move=> H.
have [Heq _]:= Jordan A.
pose s := [seq (x.2).-1 | x <- root_seq_poly (invariant_factors A)].
have Hs: size ([seq (Jordan_form A) i i | i <- enum 'I_(size_sum s).+1]) = n.+1.
  by rewrite size_map size_enum_ord.
have Hn i: nth 0%N s i = 0%N.
  case: (ltnP i (size (root_seq_poly (invariant_factors A))))=> Hi.
    rewrite (nth_map (0,0%N)) //.
    have/flattenP [s2 Hd Hs2] := (mem_nth (0,0%N) Hi); move: Hd.
    case/(nthP nil)=> m; rewrite !size_map=> Hm Heq2.
    move: Heq2 Hs2; rewrite (nth_map 0) // => <-.
    move=> Hr; rewrite (uniq_root_mu_seq _ Hr) //.
    apply: (uniq_root_dvdp _ H).
      by rewrite monic_neq0 // mxminpoly_monic.
    rewrite -mxminpoly_inv_factors Frobenius_seqE last_cat -nth_last.
    have Hif: (0 < (size (invariant_factors A)))%N.
      by rewrite lt0n size_eq0 nnil_inv_factors.
    rewrite (set_nth_default 0) ?prednK //.
    apply: sorted_leq_nth=> //.
      -exact: dvdp_trans.
      -exact: sorted_invf.
      -by rewrite inE prednK.
    by rewrite -ltnS prednK.
  by rewrite nth_default // size_map.
apply: (similar_trans (Jordan A)).
apply: (similar_trans _ (similar_diag_mx_seq (erefl n.+1) Hs (eigen_diag A))).
rewrite /Jordan_form diag_block_mx_seq //.
rewrite size_map size_enum_ord in Hs.
rewrite Hs.
set s1 := mkseq _ _.
set s2 := map _ _.
have ->: s2 = s1.
  apply: (@eq_from_nth _ 0).
    rewrite size_map size_enum_ord Heq size_mkseq.
    rewrite size_sum_big.
      rewrite (eq_big_seq (fun _ => 1%N)).
        by rewrite (big_nth 0%N) sum_nat_const_nat subn0 muln1.
      by move=> x /(nthP 0%N) [i Hi]; rewrite Hn=> <-.
    rewrite -size_eq0 size_map size_flatten sumn_big !big_map.
    have H0: (0 < (size (invariant_factors A)))%N.
      by rewrite lt0n size_eq0 nnil_inv_factors.
    rewrite (big_nth 0) big_mkord (bigD1 (Ordinal H0)) //.
    rewrite size_map -lt0n addn_gt0 lt0n size_eq0.
    apply/orP; left; apply/eqP=>/undup_nil; apply/eqP.
    rewrite -root_seq_nil -ltnNge.
    have:= (mem_nth 0 H0).
    by rewrite mem_filter; case/andP=> ->.
  move=> i; rewrite size_map size_enum_ord=> Hi.
  rewrite (nth_map 0) ?size_enum_ord //.
  by rewrite (nth_ord_enum 0 (Ordinal Hi)) !mxE eqxx.
exact: similar_refl.
Qed.

Lemma ex_diagonalization n (A : 'M[R]_n.+1) : uniq (root_seq (mxminpoly A)) ->
  {s | similar A (diag_mx_seq n.+1 n.+1 s)}.
Proof.
move=> H; exists (root_seq (char_poly A)).
exact: diagonalization.
Qed.

End jordan.
