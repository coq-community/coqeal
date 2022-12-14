(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
(* Formalization of the Sasaki-Murao algorithm *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path ssralg.
From mathcomp Require Import fintype perm choice matrix bigop zmodp poly polydiv mxpoly.

From CoqEAL Require Import ssrcomplements minor dvdring.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* First some general lemmas *)
Section prelude.

Variable R : comRingType.

Lemma bareiss_key_lemma m d l (c : 'cV[R]_m) M :
  d ^+ m * \det (block_mx d%:M l c M) = d * \det (d *: M - c *m l).
Proof.
rewrite -[d ^+ m]mul1r -det_scalar -(det1 _ 1) -(det_ublock _ 0) -det_mulmx.
rewrite mulmx_block ?(mul0mx,addr0,add0r,mul1mx,mul_scalar_mx) -2![LHS]mul1r.
rewrite -{1}(@det1 _ 1) -{2}(@det1 _ m) mulrA -(@det_lblock _ _ _ _ (- c)).
rewrite -det_mulmx mulmx_block ?(mul1mx,mul0mx,addr0) addrC mul_mx_scalar.
by rewrite scalerN subrr det_ublock det_scalar1 addrC mulNmx.
Qed.

(* The key lemma of our proof: after simplification, all the k-minors *)
(* (involving 1st line/column) can be divided by (M 0 0)^k *)
Lemma bareiss_key_lemma_sub m n k d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n))
  (f1: 'I_k -> 'I_m) (f2: 'I_k -> 'I_n):
  d * (minor f1 f2 (d *: M - c *m l)) =
  d ^+ k * (minor (lift_pred f1) (lift_pred f2) (block_mx d%:M l c M)).
Proof.
by rewrite /minor submatrix_lift_block bareiss_key_lemma
  submatrix_add submatrix_scale submatrix_opp submatrix_mul.
Qed.

Lemma bareiss_block_key_lemma_sub m n k (M : 'M[R]_(1 + m,1 + n))
  (f : 'I_k -> 'I_m) (g : 'I_k -> 'I_n) :
  M 0 0 * (minor f g (M 0 0 *: drsubmx M - dlsubmx M *m ursubmx M)) =
  M 0 0 ^+ k * (minor (lift_pred f) (lift_pred g) M).
Proof.
rewrite /minor -{7}[M]submxK submatrix_add submatrix_scale submatrix_opp.
have -> : ulsubmx M = (M 0 0)%:M by apply/rowP=> i; rewrite ord1 !mxE !lshift0.
by rewrite submatrix_lift_block bareiss_key_lemma submatrix_mul.
Qed.


End prelude.

Require Import polydvd.

Module poly.
Section bareiss.

Variable R : comRingType.

Fixpoint bareiss_rec m (a : {poly R}) :
   'M[{poly R}]_(1 + m, 1 + m) -> {poly R} :=
  if m is p.+1 then
    fun M =>
      let d   := M 0 0 in
      let l   := ursubmx M in
      let c   := dlsubmx M in
      let N   := drsubmx M in
      let M'  := d *: N - c *m l in
      let M'' := map_mx (fun x => rdivp x a) M' in
      bareiss_rec d M''
  else fun M => M 0 0.

Definition bareiss n (M : 'M_(1 + n, 1 + n)) : {poly R} := bareiss_rec 1 M.

Definition bareiss_char_poly n (M : 'M_(1 + n, 1 + n)) : {poly R} :=
  bareiss (char_poly_mx M).

(* The actual determinant function based on Bareiss *)
Definition bdet n (M : 'M_(1 + n, 1 + n)) : R :=
  (bareiss_char_poly (- M))`_0.

End bareiss.

Section bareiss_correctness.

Variable R : comRingType.

Lemma bareiss_recE : forall m a (M : 'M[{poly R}]_(1 + m)),
  a \is monic ->
  (forall p (h h' : p < 1 + m), pminor h h' M \is monic) ->
  (forall k (f g : 'I_k.+1 -> 'I_m.+1), rdvdp (a ^+ k) (minor f g M)) ->
  a ^+ m * (bareiss_rec a M) = \det M.
Proof.
elim=> [a M _ _ _|m ih a M am hpm hdvd] /=.
  by rewrite expr0 mul1r {2}[M]mx11_scalar det_scalar1.
have ak_monic k : a ^+ k \is monic by apply/monic_exp.
set d := M 0 0; set M' := (_ - _); set M'' := map_mx _ _; rewrite /= in M' M'' *.
have d_monic : d \is monic.
  have -> // : d = pminor (ltn0Sn _) (ltn0Sn _) M.
  have h : widen_ord (ltn0Sn m.+1) =1 (fun=> 0)
    by move=> x; apply/ord_inj; rewrite [x]ord1.
  by rewrite /pminor (minor_eq h h) minor1.
have dk_monic : forall k, d ^+ k \is monic by move=> k; apply/monic_exp.
have hM' : M' = a *: M''.
  pose f := fun m (i : 'I_m) (x : 'I_2) => if x == 0 then 0 else lift 0 i.
  apply/matrixP => i j.
  rewrite !mxE big_ord1 !rshift1 [a * _]mulrC rdivpK ?(eqP am,expr1n,mulr1) //.
  move: (hdvd 1%nat (f _ i) (f _ j)).
  by rewrite !minor2 /f /= expr1 !mxE !lshift0 !rshift1.
rewrite -[M]submxK; apply/(@lregX _ d m.+1 (monic_lreg d_monic)).
have -> : matrix.ulsubmx M = d%:M by apply/rowP=> i; rewrite !mxE ord1 lshift0.
rewrite bareiss_key_lemma -/M' hM' detZ mulrCA [_ * (a ^+ _ * _)]mulrCA !exprS -!mulrA.
rewrite ih // => [p h h'|k f g].
  rewrite -(@monicMl _ (a ^+ p.+1)) // -detZ -submatrix_scale -hM'.
  rewrite -(monicMl _ d_monic) bareiss_block_key_lemma_sub monicMr //.
  by rewrite (minor_eq (lift_pred_widen_ord h) (lift_pred_widen_ord h')) hpm.
case/rdvdpP: (hdvd _ (lift_pred f) (lift_pred g)) => // x hx.
apply/rdvdpP => //; exists x.
apply/(@lregX _ _ k.+1 (monic_lreg am))/(monic_lreg d_monic).
rewrite -detZ -submatrix_scale -hM' bareiss_block_key_lemma_sub.
by rewrite mulrA [x * _]mulrC mulrACA -exprS [_ * x]mulrC -hx.
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
rewrite /bdet bareiss_char_polyE char_poly_det.
by rewrite -scaleN1r detZ mulrA -expr2 sqrr_sign mul1r.
Qed.

End bareiss_correctness.
End poly.

Module dvdring.
Section Bareiss2.
Variable R: dvdRingType.

Definition dvd_step (m n:nat) (d: R) (M: 'M[R]_(m,n)) : 'M[R]_(m,n) :=
  map_mx (fun x => odflt 0 (x %/? d)) M.

(*
  determinant equality for division step
*)
Lemma det_dvd_step: forall n a (M: 'M[R]_n),
  (forall i j, a %| M i j) ->
  a^+n * \det (dvd_step a M) = \det M.
Proof.
rewrite /dvd_step => n a M hj.
rewrite -detZ; f_equal.
apply/matrixP => i j; rewrite !mxE.
case: odivrP=>[d|h] /=; first by rewrite mulrC.
case/dvdrP: (hj i j) => d hd.
by move: (h d); rewrite hd eqxx.
Qed.

Lemma det_dvd_step_tool : forall m n a (M N: 'M[R]_(m,n)),
  M = a *: N -> forall i j, a %| M i j.
Proof.
move => m n a M N /matrixP h i j.
rewrite (h i j) !mxE mulrC.
by apply/dvdr_mull/dvdrr.
Qed.

Let lreg := GRing.lreg.

(*
  some rewriting lemmas to make the main proof more clear
*)
Lemma blockE00 m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)):
   (block_mx d%:M l c M) 0 0 = d.
Proof.
rewrite !mxE.
case: splitP => x //; rewrite [x]ord1 {x} !mxE => _.
by case: splitP => x //; rewrite [x]ord1 {x} !mxE => _.
Qed.

Lemma blockE0i m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)) i:
  (block_mx d%:M l c M) 0 (lift 0 i) = (l 0 i).
Proof.
rewrite !mxE.
case: splitP => x //; rewrite [x]ord1 {x} !mxE => _.
case: splitP => x; first by rewrite [x]ord1.
by rewrite /= /bump /leq0n => /eqP; rewrite eqSS => /eqP/ord_inj->.
Qed.

Lemma blockEi0 m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)) i:
  (block_mx d%:M l c M) (lift 0 i) 0 = (c i 0).
Proof.
rewrite !mxE.
case: splitP => x; first by rewrite [x]ord1.
rewrite /= /bump /leq0n => /eqP; rewrite eqSS => /eqP/ord_inj->.
rewrite !mxE.
by case: splitP => y //; rewrite [y]ord1 {y} => _.
Qed.

Lemma blockEij m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)) i j:
  (block_mx d%:M l c M) (lift 0 i) (lift 0 j) = (M i j).
Proof.
rewrite !mxE.
case: splitP => x; first by rewrite [x]ord1.
rewrite /= /bump /leq0n => /eqP; rewrite eqSS =>  /eqP/ord_inj->.
rewrite !mxE.
case: splitP => y; first by rewrite [y]ord1.
by rewrite /= /bump /leq0n => /eqP; rewrite eqSS =>  /eqP/ord_inj->.
Qed.

(*
  main step of the proof
*)
Lemma sketch m n (a d: R) (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)):
 lreg a ->
 (forall (k:nat) (f1: 'I_k.+1 -> 'I_(1 + m)) (f2: 'I_k.+1 -> 'I_(1 + n)),
     a ^+ k %| minor f1 f2 (block_mx d%:M l c M))->
 (forall p (h: p.+1 <= 1 + m) (h': p.+1 <= 1 + n),
   lreg (pminor h h' (block_mx d%:M l c M))) ->
   let M' := d *: M - c *m l in
   let M'':= dvd_step a M' in
     [/\ lreg d,
       (forall k (f1: 'I_k.+1 -> 'I_m) (f2: 'I_k.+1 -> 'I_n),
         d ^+ k %| minor f1 f2 M''),
       M' = a *: M'' &
  (forall p (h: p.+1 <= m) (h': p.+1 <= n),
   lreg (pminor h h' M''))].
Proof.
rewrite /pminor => ha hM hN.
set M0 := block_mx d%:M l c M.
(* d is the 1x1 principal minor of M0 *)
have hh : d = minor (widen_ord (ltn0Sn _)) (widen_ord (ltn0Sn _)) M0.
- rewrite (@minor_eq _ _ _ _ _ (fun _ => 0) _ (fun _ => 0)) ?minor1 //.
  + by rewrite /M0 blockE00.
  + by move => x; rewrite ord1; apply: val_inj.
  + by move => x; rewrite ord1; apply: val_inj.
(* all principal minors of M0 are lreg, so M 0 0 is *)
have h2 : lreg d.
- by rewrite hh /M0; apply hN.
set M' := d *: M - c *m l.
set M'' := dvd_step a M'.
set f : forall m, 'I_m -> 'I_2 -> 'I_(1 + m) :=
  fun m (i: 'I_m) (x: 'I_2) => if x == 0 then 0 else (lift 0 i).
(*
  all elements of M' can be expressed as 2x2 minors of M,
  so a divide all these
*)
have h4 : forall i j, a %| M' i j.
- move => i j; rewrite /M' !mxE big_ord_recl big_ord0 addr0.
  move: (hM 1%nat (f _ i) (f _ j)). (* (hstrict _ i)). *)
  by rewrite !minor2 /f /= expr1 blockE00 blockEi0 blockE0i blockEij.
(*
  since a divides all M' i j, all the divisions are exact,
  and thus M' = a * M''
*)
have h6 : forall i j, M' i j = a * M'' i j.
- move => i j; rewrite [(dvd_step _ _) i j]mxE.
  case: odivrP => [dv|h] /=; first by rewrite mulrC.
  case/dvdrP: (h4 i j) => dv hdv.
  by move: (h dv); rewrite hdv eqxx.
have h6' : M' = a *: M'' by apply/matrixP => i j; rewrite h6 !mxE.
(*
  from this equality, we can have more information about the minors
  of M' and M''
*)
have h7 : forall k (f1: 'I_k -> 'I_m) (f2: 'I_k -> 'I_n),
    minor f1 f2 M' = a ^+ k * minor f1 f2 M''.
- move => k f1 f2.
  by rewrite h6' /minor submatrix_scale detZ.
(*
  using all theses, we can now prove our goals
*)
have h8: forall k (f1: 'I_k -> 'I_m) (f2: 'I_k -> 'I_n),
  d * minor f1 f2 M' =
    d ^+ k * minor (lift_pred f1) (lift_pred f2) M0.
- move => k f1 f2.
  by rewrite /M0 /M' bareiss_key_lemma_sub.
have ak : forall k, lreg (a^+k).
- by move => k; apply/lregX.
have h10 : forall k (f1: 'I_k.+1 -> 'I_m) (f2: 'I_k.+1 -> 'I_n),
  d ^+ k %| minor f1 f2 M''.
- move => k f1 f2.
  move/lregP : (ak k.+1) => ak'.
  rewrite -(@dvdr_mul2l _ (a^+k.+1)) // -h7.
  have hM0 : d != 0 by apply/lregP.
  have hMk : d^+ k.+1 != 0 by apply/lregP/lregX.
  rewrite -(@dvdr_mul2l _ d) // mulrA h8 //.
  by rewrite mulrAC -exprS dvdr_mul2l //.
split=> //.
rewrite -/M'' => p h h'.
apply/(@lregMl _ (a ^+ p.+1)).
rewrite -h7.
apply/(@lregMl _ d).
rewrite h8.
apply/lregM; first by apply/lregX.
rewrite (@minor_eq _ _ _ _ _ (widen_ord (size_tool h)) _
                             (widen_ord (size_tool h'))) ?hN.
- by apply: hN.
- by move => x; apply: val_inj; rewrite lift_pred_widen_ord.
- by move => x; apply: val_inj; rewrite lift_pred_widen_ord.
Qed.


(*
  formal definition of bareiss algorithm
*)
Fixpoint bareiss_rec m a : 'M[R]_(1 + m) -> R :=
  if m is p.+1 return 'M[R]_(1 + m) -> R then
    fun (M: 'M[R]_(1 + _)) =>
      let d   := M 0 0 in
      let l   := ursubmx M in
      let c   := dlsubmx M in
      let N   := drsubmx M in
      let M'  := d *: N - c *m l in
      let M'' := dvd_step a M' in
      bareiss_rec d M''
  else fun M => M 0 0.

(*
  from sketch, we can express the properties of bareiss
*)
Lemma bareiss_recE : forall m a (M: 'M[R]_(1 + m)),
    lreg a  ->
 (forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_m.+1), a ^+ k %| minor f1 f2 M) ->
 (forall p  (h h' :p.+1 <= 1 + m),
   lreg (minor (widen_ord h) (widen_ord h') M)) ->
    a ^+ m * (bareiss_rec a M) = \det M.
Proof.
elim => [ | m hi] //=.
- move => a M ha h1 h2.
  by rewrite expr0 {2}[M]mx11_scalar det_scalar1 mul1r.
rewrite [(1 + m.+1)%nat]/(1 + (1 + m))%nat => a M ha.
set d := M 0 0.
set l := ursubmx M.
set c := dlsubmx M.
set N := drsubmx M.
have heq : block_mx (M 0 0)%:M (ursubmx M) (dlsubmx M) (drsubmx M) = M.
- have -> : (M 0 0)%:M = ulsubmx M
  by apply/matrixP => i j; rewrite !mxE [i]ord1 [j]ord1 {i j} !lshift0.
  by rewrite submxK.
rewrite -{1 2}heq => hM hm.
have : forall p (h h': p.+1 <= 1 + (1 + m)),
  lreg (minor (widen_ord h) (widen_ord h') M).
- rewrite -heq => p h h'.
  rewrite (@minor_eq _ _ _ _ _ (widen_ord h) _ (widen_ord h)) ?hm//.
  by move => x; apply/ord_inj.
case: (@sketch _ _ a (M 0 0) (ursubmx M) (dlsubmx M) (drsubmx M) ha hM hm)
 => hM00 h1 h2 h3 hlreg.
have h3' : forall p (h h': p < 1 + m),
  lreg (pminor h h' (dvd_step a (d *: N - c *m l)))
 by  move => p h h'; apply/h3.
move: (hi d (dvd_step a (d *: N - c *m l)) hM00 h1 h3').
set r := bareiss_rec _ _ => hh.
have : a ^+ m.+1 *( d ^+m * r) =
       a ^+ m.+1 * \det (dvd_step a (d *: N - c *m l)) by rewrite hh.
rewrite det_dvd_step //; last by
  move => i j; apply (det_dvd_step_tool h2).
move => heq2.
have hX : lreg (M 0 0 ^+ (1 + m)) by apply/lregX.
apply/hX.
rewrite -{3}heq bareiss_key_lemma -heq2 [M 0 0 ^+ (1 + m)]exprS -mulrA.
congr(_ * _).
by rewrite mulrCA.
Qed.

(*
  we start the algorithm with a = 1
*)
Definition bareiss (n: nat) (M: 'M[R]_(1 + n)) :=
  bareiss_rec 1 M.

Lemma bareissE : forall n (M: 'M[R]_(1 + n)),
 (forall p (h h': p.+1 <= 1 + n), lreg (pminor h h' M)) ->
  bareiss M = \det M.
Proof.
rewrite /bareiss => n M h.
have h1 : lreg (1: R) by apply/lreg1.
have h2 : forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_n.+1),
     1 ^+ k %| minor f1 f2 M.
- by move => k f1 f2; rewrite expr1n dvd1r.
move: (bareiss_recE h1 h2 h).
by rewrite expr1n mul1r.
Qed.

End Bareiss2.

(*
  In practice, we apply this algorithm to the characteristic matrix
  so we get the characteristic polynomial in polynomial time
*)
Import PolyDvdRing.

Section bareiss_det.
Variable R: dvdRingType.

(*
  all principal minor of the characteristic matrix are monic
*)
Lemma pminor_char_poly_mx_monic: forall m p (M: 'M[R]_m) (h h': p.+1 <= m),
  pminor h h' (char_poly_mx M) \is monic.
Proof.
rewrite /pminor => m p M h h'.
rewrite (@minor_eq _ _ _ _ _ (widen_ord h) _ (widen_ord h)); first last.
- by apply: widen_ord_eq.
- by move => x.
rewrite /minor submatrix_char_poly_mx; last by apply: inj_widen_ord.
by apply/char_poly_monic.
Qed.


Definition char_poly_alt n (M: 'M[R]_(1 + n)) :=
  bareiss (char_poly_mx M).

(*
  Here is our alternative definition of char_poly
*)
Lemma char_poly_altE : forall n (M: 'M[R]_(1 + n)),
  char_poly_alt M = char_poly M.
Proof.
rewrite /char_poly_alt /char_poly => n M.
by rewrite bareissE // => p h h'; exact/monic_lreg/pminor_char_poly_mx_monic.
Qed.

(* The actual determinant function based on bareiss *)
Definition bdet n (M : 'M[R]_(1 + n)) := (char_poly_alt (-M))`_0.

Lemma bdetE : forall n (M : 'M[R]_(1 + n)), bdet M = \det M.
Proof.
move=> n M.
rewrite /bdet char_poly_altE char_poly_det.
have -> : - M = -1 *: M by apply/matrixP => i j; rewrite !mxE mulN1r.
by rewrite detZ mulrA -expr2 sqrr_sign mul1r.
Qed.

End bareiss_det.
End dvdring.
