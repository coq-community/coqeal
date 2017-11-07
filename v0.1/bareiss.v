(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
(* Formalization of Sasaki-Murao algorithm - Not ported to CoqEAL 2.0 yet *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path ssralg.
Require Import fintype perm choice matrix bigop zmodp poly polydiv mxpoly.

Require Import minor.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(* Clean version of Bareiss *)
Section bareiss_def.

Variable R : comRingType.

Fixpoint bareiss_rec m a : 'M[{poly R}]_(1 + m) -> {poly R} :=
  match m return 'M[_]_(1 + m) -> {poly R} with
    | S p => fun (M: 'M[_]_(1 + _)) =>
      let d   := M 0 0 in
      let l   := ursubmx M in
      let c   := dlsubmx M in
      let N   := drsubmx M in
      let M'  := d *: N - c *m l in
      let M'' := map_mx (fun x => rdivp x a) M' in
        bareiss_rec d M''
    | _ => fun M => M 0 0
  end.

Definition bareiss n (M : 'M[{poly R}]_(1 + n)) := bareiss_rec 1 M.

Definition bareiss_char_poly n (M : 'M[R]_(1 + n)) := bareiss (char_poly_mx M).

(* The actual determinant function based on Bareiss *)
Definition bdet n (M : 'M[R]_(1 + n)) := (bareiss_char_poly (-M))`_0.

End bareiss_def.

Section bareiss_correctness.

(* First some general lemmas *)
Section bareiss_comRingType.

Variable R : comRingType.

Lemma key_lemma m d l (c : 'cV[R]_m) M :
  d ^+ m * \det (block_mx d%:M l c M) = d * \det (d *: M - c *m l).
Proof.
rewrite -[d ^+ m]mul1r -det_scalar -(det1 _ 1) -(det_ublock _ 0) -det_mulmx.
rewrite mulmx_block ?(mul0mx,addr0,add0r,mul1mx,mul_scalar_mx) -2![LHS]mul1r.
rewrite -{1}(@det1 _ 1) -{2}(@det1 _ m) mulrA -(@det_lblock _ _ _ _ (- c)).
rewrite -det_mulmx mulmx_block ?(mul1mx,mul0mx,addr0) addrC mul_mx_scalar.
by rewrite scalerN subrr det_ublock det_scalar1 addrC mulNmx.
Qed.

(* The key lemma of our proof: after simplification, all the k-minors (involving *)
(* 1st line/column) can be divided by (M 0 0)^k *)
Lemma key_lemma_sub m n k (M : 'M[R]_(1 + m,1 + n))
  (f : 'I_k -> 'I_m) (g : 'I_k -> 'I_n) :
  M 0 0 * (minor f g (M 0 0 *: drsubmx M - dlsubmx M *m ursubmx M)) =
  M 0 0 ^+ k * (minor (lift_pred f) (lift_pred g) M).
Proof.
rewrite /minor -{7}[M]submxK submatrix_add submatrix_scale submatrix_opp.
have -> : ulsubmx M = (M 0 0)%:M by apply/rowP=> i; rewrite ord1 !mxE !lshift0.
by rewrite submatrix_lift_block key_lemma submatrix_mul.
Qed.

End bareiss_comRingType.

(* Switch to polynomials over a commutative ring *)
Section bareiss_poly.

Variable R : comRingType.

(* Why is this not in the libraries? *)
Lemma monic_lreg (p : {poly R}) : p \is monic -> GRing.lreg p.
Proof. by rewrite monicE=> /eqP h; apply/lreg_lead; rewrite h; apply/lreg1. Qed.

Lemma bareiss_recE : forall m a (M : 'M[{poly R}]_(1 + m)),
  a \is monic ->
 (forall p (h h' : p < 1 + m), pminor h h' M \is monic) ->
 (forall k (f g : 'I_k.+1 -> 'I_m.+1), rdvdp (a ^+ k) (minor f g M)) ->
  a ^+ m * (bareiss_rec a M) = \det M.
Proof.
elim=> [a M _ _ _|m ih a M am hpm hdvd] /=.
  by rewrite expr0 mul1r {2}[M]mx11_scalar det_scalar1.
have ak_monic k : a ^+ k \is monic by apply/monic_exp.
set d := M 0 0; set M' := _ - _; set M'' := map_mx _ _; simpl in M'.
have d_monic : d \is monic.
  have -> // : d = pminor (ltn0Sn _) (ltn0Sn _) M.
  have h : widen_ord (ltn0Sn m.+1) =1 (fun _ => 0)
    by move=> x; apply/ord_inj; rewrite [x]ord1.
  by rewrite /pminor (minor_eq _ h h) minor1.
have dk_monic : forall k, d ^+ k \is monic by move=> k; apply/monic_exp.
have hM' : M' = a *: M''.
  pose f := fun m (i : 'I_m) (x : 'I_2) => if x == 0 then 0 else (lift 0 i).
  apply/matrixP => i j.
  rewrite !mxE big_ord1 !rshift1 [a * _]mulrC rdivpK ?(eqP am,expr1n,mulr1) //.
  move: (hdvd 1%nat (f _ i) (f _ j)).
  by rewrite !minor2 /f /= expr1 !mxE !lshift0 !rshift1.
rewrite -[M]submxK; apply/(@lregX _ d m.+1 (monic_lreg d_monic)).
have -> : ulsubmx M = d%:M by apply/rowP=> i; rewrite !mxE ord1 lshift0.
rewrite key_lemma -/M' hM' detZ mulrCA [_ * (a ^+ _ * _)]mulrCA !exprS -!mulrA.
rewrite ih // => [p h h'|k f g].
  rewrite -(@monicMl _ (a ^+ p.+1)) // -detZ -submatrix_scale -hM'.
  rewrite -(monicMl _ d_monic) key_lemma_sub monicMr //.
  by rewrite (minor_eq _ (lift_pred_widen_ord h) (lift_pred_widen_ord h')) hpm.
case/rdvdpP: (hdvd _ (lift_pred f) (lift_pred g)) => // x hx.
apply/rdvdpP => //; exists x.
apply/(@lregX _ _ k.+1 (monic_lreg am))/(monic_lreg d_monic).
rewrite -detZ -submatrix_scale -hM' key_lemma_sub mulrA [x * _]mulrC mulrACA.
by rewrite -exprS [_ * x]mulrC -hx.
Qed.

Lemma bareissE n (M : 'M[{poly R}]_(1 + n)) 
  (H : forall p (h h' : p < 1 + n), pminor h h' M \is monic) :
  bareiss M = \det M.
Proof.
rewrite /bareiss -(@bareiss_recE n 1 M) ?monic1 ?expr1n ?mul1r //.
by move=> k f g; rewrite expr1n rdvd1p.
Qed.

Lemma bareiss_char_polyE n (M : 'M[R]_(1 + n)) : 
  bareiss_char_poly M = char_poly M.
Proof.
rewrite /bareiss_char_poly bareissE // => p h h'.
exact: pminor_char_poly_mx_monic.
Qed.

Lemma bdetE n (M : 'M[R]_(1 + n)) : bdet M = \det M.
Proof.
rewrite /bdet bareiss_char_polyE char_poly_det -scaleN1r detZ mulrA -expr2.
by rewrite sqrr_sign mul1r.
Qed.

End bareiss_poly.
End bareiss_correctness.
