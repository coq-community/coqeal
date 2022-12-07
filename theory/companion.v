From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From CoqEAL Require Import ssrcomplements mxstructure.

(**  This file defines companion matrices for any non-constant polynomial and
  prooves the properties of their characteristic and minimal polynomials

     companion_mx p == The companion matrix of the polynomial p.

                                                                              *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Companion.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable R : comRingType.

Definition companion_mxn n (p : {poly R}) :=
  \matrix_(i, j < n ) ((i == j.+1 :> nat)%:R
    - p`_i *+ ((size p).-2 == j)).

Definition companion_mx (p : {poly R}) := companion_mxn (size p).-2.+1 p.

Lemma comp_char_polyK : forall (p : {poly R}), p \is monic ->
  (1 < size p)%N -> char_poly (companion_mx p) = p.
Proof.
apply: poly_ind=> [|p c IHp]; first by move/monic_neq0/eqP.
have [-> H | p0 Hm Hs] := eqVneq p 0.
  by rewrite mul0r add0r {1}size_polyC; case: eqP.
have Hcst1 : (size (p * 'X + c%:P)).-1 = (size p).-1.+1.
  by rewrite size_MXaddC (negbTE p0) -polySpred.
have Hmp : p \is monic.
  rewrite monicE -lead_coefMX -(@lead_coefDl _ _ (c%:P)) -?monicE //.
  by rewrite size_polyC size_mulX // polySpred //; case:(c != 0).
case: (ltnP 1 (size p))=> Hpt; last first.
  have Hp1: p = 1%:P by rewrite -(monicP Hmp) [p]size1_polyC // lead_coefC.
  rewrite /companion_mx !Hcst1 Hp1 mul1r /char_poly size_polyC oner_eq0.
  set M := char_poly_mx _.
  rewrite [M]mx11_scalar det_scalar1 !mxE coefD coefC coefX.
  by rewrite !add0r polyCN opprK size_XaddC.
rewrite /char_poly /companion_mx Hcst1.
rewrite (expand_det_row _ ord0) big_ord_recl !mxE.
rewrite mulr1n !mulr0n add0r /cofactor !addn0 expr0 mul1r.
set d1 := \det _.
case Hnp: (size p) (Hpt)=> [|n] //; case: n Hnp=> // n Hnp _.
rewrite big_ord_recr big1; last first.
   move=> i _; rewrite !mxE !sub0r size_MXaddC (negbTE p0) andFb.
   have:= (neq_ltn n (widen_ord (leqnSn n) i)).
   rewrite Hnp (ltn_ord i) orbT lift0 eqSS.
   by move/negbTE ->; rewrite polyCN opprK mul0r.
rewrite /= add0r; set M := row' _ _.
have HM: upper_triangular_mx M.
  apply/upper_triangular_mxP=> i j Hij.
  rewrite !mxE -(inj_eq (@ord_inj _)) /= /bump !leq0n leqNgt (ltn_ord j).
  rewrite add1n eqn_leq leqNgt ltnS ltnW // sub0r eqSS eqn_leq leqNgt Hij.
  rewrite sub0r eqn_leq size_MXaddC (negbTE p0) andFb Hnp.
  by rewrite  (leqNgt n.+1) (ltn_ord j) polyCN opprK.
have->: \det M = (-1)^+n.+1.
  rewrite (det_triangular_mx HM) -{7}[n.+1]card_ord -prodr_const.
  apply: eq_bigr=> i _; rewrite !mxE -(inj_eq (@ord_inj _)) !lift0 !lift_max.
  rewrite eqxx !eqn_leq ltnn size_MXaddC (negbTE p0) andFb Hnp.
  by rewrite (leqNgt _ i) (ltn_ord i) sub0r subr0.
rewrite !mxE -exprD -signr_odd addnn odd_double mulr1 polyCN opprK.
rewrite size_MXaddC (negbTE p0) andFb Hnp addr0 !sub0r.
rewrite -{1}cons_poly_def coef_cons polyCN opprK !eqxx -(IHp Hmp Hpt) mulrC.
suff ->: d1 = char_poly (companion_mx p)=> //.
rewrite /companion_mx.
have ->: (size p).-2.+1 = (size p).-1.+1.-1.+1.-1 by rewrite Hnp.
congr (\det _); rewrite row'_col'_char_poly_mx; congr char_poly_mx.
apply/matrixP=> i j; rewrite !mxE !eqSS -cons_poly_def coef_cons size_cons_poly.
rewrite nil_poly (negbTE p0).
by rewrite !lift0 /= {4 9}Hnp.
Qed.

End Companion.

Section CompanionMin.

Variable F : fieldType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma comp_mxminpolyK :  forall (p : {poly F}), p \is monic ->
  (1 < size p)%N -> mxminpoly (companion_mx p) = p.
Proof.
move=> p Hp Hs.
set A := companion_mx p.
suff Hn: forall q, horner_mx A q = 0 ->
    (q == 0) || ((size p).-2 < (size q).-1)%N.
  have Hm0: (mxminpoly A == 0) = false.
    by apply: negbTE; rewrite monic_neq0 // mxminpoly_monic.
  have:= Hn (mxminpoly A) (mx_root_minpoly A); rewrite Hm0 /= => Hmn.
  have Hsm : size (mxminpoly A) == size (char_poly A).
    rewrite eqn_leq dvdp_leq ?mxminpoly_dvd_char ?monic_neq0 ?char_poly_monic //.
    by rewrite size_char_poly -(addn1 _.-2) addnC -ltn_subRL subn1.
  apply/eqP; rewrite -eqp_monic // ?mxminpoly_monic //.
  by rewrite -{2}(comp_char_polyK Hp) // -dvdp_size_eqp // mxminpoly_dvd_char.
move=> q; case: (ltnP (size p).-2 (size q).-1); first by rewrite orbT.
have H (i : 'I_(size p).-2):
  A *m col (widen_ord (leqnSn (size p).-2) i) 1%:M = col (lift ord0 i) 1%:M.
  rewrite col_id_mulmx; apply/matrixP=> j k; rewrite !mxE.
  rewrite -(inj_eq (@ord_inj _)) lift0.
  by rewrite (eqn_leq _ i) (leqNgt _ i) (ltn_ord i) subr0.
have H2: forall i : 'I_(size p).-2.+1, (A ^+ i) *m col ord0 1%:M = col i 1%:M.
  case; elim=> [Hi|i IH Hi] /=.
    by rewrite expr0 mul1mx; congr col; apply: ord_inj.
  rewrite exprS -mulmxA (IH (ltnW Hi)).
  have Ho: (i < (size p).-2)%N by rewrite -ltnS.
  have ->: (Ordinal (ltnW Hi)) = (widen_ord (leqnSn (size p).-2) (Ordinal Ho)).
    by apply: ord_inj.
  by rewrite H; congr col; apply: ord_inj; rewrite lift0.
case Hq: (q == 0)=> //.
have Hsq: (0 < size q)%N by rewrite size_poly_gt0 Hq.
rewrite /horner_mx /horner_morph horner_coef.
rewrite size_map_poly_id0 ?fmorph_eq0 ?lead_coef_eq0 ?Hq // => H1 Hb.
have Hw: (size q <= (size p).-2.+1)%N by rewrite -(prednK Hsq).
suff : q == 0 by rewrite Hq.
have: \sum_(i < size q) q`_i *: (A ^+ i *m col ord0 1%:M) = 0.
  rewrite (eq_bigr (fun i : 'I_(size q) =>
                    ((map_poly scalar_mx q)`_i * A ^+ i) *m col ord0 1%:M)).
    by rewrite -mulmx_suml ?Hb ?mul0mx //.
  by move=> i _; rewrite coef_map scalemxAl -mul_scalar_mx.
set b := \sum_(_ < _) _.
have <-: \col_(i < (size p).-2.+1) q`_i = b.
  apply/matrixP=> i j; rewrite mxE summxE.
  case: (ltnP i (size q))=> Hi.
    rewrite (bigD1 (Ordinal Hi)) //= H2 !mxE eqxx mulr1 big1 ?addr0 //.
    move=> k Hk; rewrite (H2 (widen_ord Hw k)) !mxE.
    move/negbTE: Hk; rewrite -!(inj_eq (@ord_inj _)) /= eq_sym=> ->.
    by rewrite mulr0.
  rewrite nth_default // big1 // => k _.
  rewrite (H2 (widen_ord Hw k)) !mxE -(inj_eq (@ord_inj _)) /= eqn_leq.
  by rewrite leqNgt (leq_trans (ltn_ord k) Hi) andFb mulr0.
move/matrixP=> Hc.
apply/eqP/size_poly_leq0P/leq_sizeP=> j _.
case: (ltnP j (size p).-2.+1)=> Hj.
  by move: (Hc (Ordinal Hj) ord0); rewrite !mxE.
by rewrite nth_default //; apply: leq_trans Hj.
Qed.

End CompanionMin.
