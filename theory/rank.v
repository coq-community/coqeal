(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import ssralg fintype fingroup perm.
From mathcomp Require Import matrix bigop zmodp mxalgebra.

Require Import gauss.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FieldRank.

Variable F : fieldType.
Local Open Scope ring_scope.

Fixpoint rank_elim {m n : nat} : 'M[F]_(m, n) -> nat :=
  if n is p.+1 then
    fun (M : 'M_(m, 1 + p)) =>
      if find_pivot M is Some k then
        let a := fun_of_matrix M k 0 in
        let u := rsubmx (row k M) in
        let R := row' k M in
        let v := a^-1 *: lsubmx R in
        let R := rsubmx R - v *m u in
        (1 + rank_elim R)%N
      else rank_elim (rsubmx M)
  else fun => 0%N.

Lemma rank_row0mx (m n p : nat) (M : 'M[F]_(m,n)) :
  \rank (row_mx (0: 'M[F]_(m,p)) M) = \rank M.
Proof. by rewrite -mxrank_tr tr_row_mx trmx0 -addsmxE adds0mx mxrank_tr. Qed.

Lemma rank_block0dl m n a Aur (Adr : 'M[F]_(m,n)) :
  a != 0 -> \rank (block_mx (a%:M : 'M_1) Aur 0 Adr) = (1 + \rank Adr)%N.
Proof.
move=> nz_a.
rewrite /block_mx -addsmxE mxrank_disjoint_sum.
  rewrite rank_row0mx rank_rV.
  have->//: row_mx a%:M Aur != 0.
    apply/eqP => /matrixP/(_ 0 0); rewrite !mxE.
    by case: splitP => // j _; rewrite ord1 !mxE; move/eqP: nz_a.
apply/eqP/rowV0P => v0; rewrite sub_capmx; case/andP=> /sub_rVP [k Hv0k].
rewrite Hv0k; case/submxP => D /matrixP/(_ 0 0); rewrite !mxE.
case: splitP => // j _; rewrite ord1 mxE mulr1n big1.
by move/eqP; rewrite mulf_eq0 (negbTE nz_a) orbF => /eqP ->; rewrite scale0r.
by move=> i _; rewrite !mxE; case: splitP=> // l _; rewrite mxE mulr0.
Qed.

Lemma row'_row_perm m n M k :
  row' k M = dsubmx (row_perm (lift_perm 0 k 1%g) M : 'M[F]_(1 + m, n)).
Proof.
by apply/matrixP=> i j; rewrite !mxE rshift1 lift_perm_lift perm1.
Qed.

Lemma row_row_perm m n (M : 'M[F]_(1 + m, n)) k :
  row k M = @usubmx _ 1 _ _ (row_perm (lift_perm 0 k 1%g) M).
Proof.
by apply/matrixP=> i j; rewrite !mxE ord1 lshift0 lift_perm_id.
Qed.

Lemma rank_elimP m n (M : 'M_(m, n)) : rank_elim M = \rank M.
Proof.
elim: n m M => [m M|n IHn m]; first by rewrite thinmx0 mxrank0.
rewrite -[n.+1]/(1 + n)%N => M /=.
rewrite /find_pivot.
have [|nz_Mk0] /= := pickP; last first.
  rewrite -{2}[M]hsubmxK.
  suff->: lsubmx M = 0 by rewrite rank_row0mx.
  apply/matrixP => i j; rewrite !mxE ord1 lshift0.
  by have /(_ i)/negbFE/eqP -> := nz_Mk0.
case: m M => [M []|m] //.
rewrite -[m.+1]/(1 + m)%N => M k /= nz_Mk0; rewrite IHn.
pose P : 'M[F]_(1 + m) := perm_mx (lift_perm 0 k 1%g).
have->: \rank M = \rank (P *m M).
  by rewrite eqmxMfull // row_full_unit unitmx_perm.
rewrite -row_permE.
set xM : 'M[F]_(1 + m, 1 + n) := row_perm _ _.
pose D : 'M[F]_(1 + m) := block_mx 1%:M 0 (- (M k 0)^-1 *: (dlsubmx xM)) 1%:M.
have hD : row_full D.
  by rewrite row_full_unit unitmxE !det_lblock !det1 !mul1r unitr1.
rewrite -(eqmxMfull xM hD) -[xM]submxK mulmx_block !mul1mx !mul0mx !addr0.
rewrite scaleNr mulNmx [ulsubmx xM]mx11_scalar !mxE !lshift0 lift_perm_id.
rewrite mul_mx_scalar scalerA divrr ?unitfE // scale1r addNr rank_block0dl //.
rewrite {3}/xM /drsubmx /dlsubmx -row'_row_perm addrC /ursubmx -row_row_perm.
by rewrite mulNmx.
Qed.

End FieldRank.
