(* Version of Bareiss/Sasaki-Murao based on dvdrings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
From mathcomp Require Import ssralg fintype perm choice.
From mathcomp Require Import matrix bigop zmodp mxalgebra poly polydiv mxpoly.

Require Import ssrcomplements dvdring minor atomic_operations.

Import Pdiv.Ring Pdiv.RingComRreg Pdiv.RingMonic GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.


Section Bareiss1.
Variable R: comRingType.

Lemma L1 m (a d: R) (l: 'rV[R]_m) (c: 'cV[R]_m) (M: 'M[R]_m):
  \det (block_mx d%:M l (a *: c) (a *: M)) =
  a ^+ m * \det (block_mx d%:M l c M).
Proof.
set X := block_mx d%:M l c M.
have huniq : uniq (map (lift 0) (enum 'I_m)).
- rewrite map_inj_in_uniq ?enum_uniq //.
  move => i j hi hj /=.
  by apply/lift_inj.
have htool : forall s, 0 \in (map (lift 0) s) -> False.
- move => n /=.
  by elim => [ | hd tl hi].
have -> : block_mx d%:M l (a *: c) (a *: M) =
  foldl (fun N i => line_scale i a N) X (map (lift 0) (enum 'I_m)).
- apply/row_matrixP => i.
  case: (lines_scale_row a X huniq) => hl hr.
  move: (hl i) (hr i) => {hl hr}.
  case: (splitP i) => j.
  + rewrite [j]ord1 {j} => hi.
    have -> : i = 0 by apply/ord_inj.
    move => _ {hi} /= ->.
    * apply/rowP => j; rewrite !mxE.
      by case: splitP.
    by apply/negP/htool.
  move => hi.
  have -> : i = lift 0 j by apply/ord_inj.
  move => -> /=.
  + move => _.
    apply/rowP => k; rewrite !mxE.
    case: splitP => x; first by rewrite [x]ord1.
    rewrite !mxE => _.
    case: splitP => y; by rewrite !mxE.
  rewrite mem_map ?mem_enum //.
  by apply/lift_inj.
by rewrite det_lines_scale size_map size_enum_ord /=.
Qed.

Definition L3tool m (c: 'cV[R]_m) (d: R) (i: 'I_(1 + m)) :=
  match split i with
    | inl _ => d
    | inr j => c j 0
  end.

Lemma L3toolE0 m (c: 'cV[R]_m) d : L3tool c d 0 = d.
Proof.
rewrite /L3tool.
by case: splitP.
Qed.

Lemma L3toolES m (c: 'cV[R]_m) d (i: 'I_m) : L3tool c d (lift 0 i) = c i 0.
Proof.
rewrite /L3tool.
case: splitP => x /=; first by rewrite [x]ord1.
rewrite /bump leq0n => /eqP; rewrite eqSS => /eqP h.
by have -> : i = x by apply/ord_inj.
Qed.

Lemma L3 m (d: R) (l: 'rV[R]_m) (c c0: 'cV[R]_m) (M: 'M[R]_m):
  \det (block_mx d%:M l c M) =
  \det (block_mx d%:M l (c - d *: c0) (M - c0 *m l)).
Proof.
pose X := block_mx d%:M l c M.
have huniq : uniq (map (lift 0) (enum 'I_m)).
- rewrite map_inj_in_uniq ?enum_uniq //.
  move => i j hi hj /=.
  by apply/lift_inj.
have htool : forall s, 0 \in (map (lift 0) s) -> False.
- move => n /=.
  by elim => [ | hd tl hi].
have htool2 : 0 \notin (map (lift 0) (enum 'I_m)).
- by apply/negP/htool.
have -> : block_mx d%:M l (c -d *: c0) (M - c0 *m l) =
  foldl (fun N i => line_comb i 0 (-(L3tool c0 d i)) N) X
        (map (lift 0) (enum 'I_m)).
- apply/row_matrixP => i.
  case: (lines_comb_row_dep (fun i => - (L3tool c0 d i)) X huniq htool2)
     => hl hr.
  move: (hl i) (hr i) => {hl hr}.
  case: (splitP i) => j.
  + rewrite [j]ord1 {j} => hi.
    have -> : i = 0 by apply/ord_inj.
    move => _ {hi i} /= -> //.
    apply/rowP => j; rewrite !mxE.
    by case: splitP.
  move => hi.
  have -> : i = lift 0 j by apply/ord_inj.
  move => -> /= {i hi}.
  + rewrite L3toolES => _.
    apply/rowP => k; rewrite !mxE.
    case: splitP => x /= ; first by rewrite [x]ord1.
    rewrite /bump leq0n => /eqP; rewrite eqSS => /eqP hjx.
    have -> : j = x by apply/ord_inj.
    case: splitP => z // {j hjx}; rewrite [z]ord1 {z} !mxE => _.
    case: splitP => y; rewrite !mxE.
    * rewrite [y]ord1 {y} => _.
      by rewrite mulrC mulr1n mulNr.
    by move => _; rewrite big_ord_recl big_ord0 addr0 mulNr.
  rewrite mem_map ?mem_enum //.
  by apply/lift_inj.
by rewrite det_lines_comb_dep // size_map size_enum_ord /=.
Qed.

Lemma key_lemma m d (l: 'rV[R]_m) (c: 'cV[R]_m) M:
  d ^+ m * \det (block_mx d%:M l c M) = d * \det (d *: M - c *m l).
Proof.
by rewrite -L1 (L3 d l (d *: c) c (d *: M)) subrr det_ublock det_scalar1.
Qed.

(*
  The key lemma of our proof: after simplification,
  all the p-minors (involving 1st line/column)
  can be divided by (M 0 0)^p-1
*)

Lemma key_lemma_sub m n k d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n))
  (f1: 'I_k -> 'I_m) (f2: 'I_k -> 'I_n):
  d * (minor f1 f2 (d *: M - c *m l)) =
  d ^+ k * (minor (lift_pred f1) (lift_pred f2) (block_mx d%:M l c M)).
Proof.
by rewrite /minor submatrix_lift_block key_lemma
  submatrix_add submatrix_scale submatrix_opp submatrix_mul.
Qed.

End Bareiss1.

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
case: odivrP.
- move => d /=; by rewrite mulrC.
move => h.
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
rewrite /= /bump /leq0n => /eqP; rewrite eqSS =>  /eqP h.
by have -> : i = x by apply/ord_inj.
Qed.

Lemma blockEi0 m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)) i:
  (block_mx d%:M l c M) (lift 0 i) 0 = (c i 0).
Proof.
rewrite !mxE.
case: splitP => x; first by rewrite [x]ord1.
rewrite /= /bump /leq0n => /eqP; rewrite eqSS =>  /eqP h.
have -> : i = x by apply/ord_inj.
rewrite !mxE.
by case: splitP => y //; rewrite [y]ord1 {y} => _.
Qed.

Lemma blockEij m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)) i j:
  (block_mx d%:M l c M) (lift 0 i) (lift 0 j) = (M i j).
Proof.
rewrite !mxE.
case: splitP => x; first by rewrite [x]ord1.
rewrite /= /bump /leq0n => /eqP; rewrite eqSS =>  /eqP h.
have -> : i = x by apply/ord_inj.
rewrite !mxE.
case: splitP => y; first by rewrite [y]ord1.
rewrite /= /bump /leq0n => /eqP; rewrite eqSS =>  /eqP h'.
by have -> : j = y by apply/ord_inj.
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
  case: odivrP.
  + move => dv /=; by rewrite mulrC.
  move => h.
  case/dvdrP: (h4 i j ) => dv hdv.
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
  by rewrite /M0 /M' key_lemma_sub.
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
split.
- exact : h2.
- exact : h10.
- exact : h6'.
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
  formal definition of Bareiss algorithm
*)
Fixpoint Bareiss_rec m a : 'M[R]_(1 + m) -> R :=
  match m return 'M[R]_(1 + m) -> R with
    | S p => fun (M: 'M[R]_(1 + _)) =>
      let d := M 0 0 in
      let l := ursubmx M in
      let c := dlsubmx M in
      let N := drsubmx M in
      let: M' := d *: N - c *m l in
      let: M'' := dvd_step a M' in
        Bareiss_rec d M''
    | _ => fun M => M 0 0
  end.

(*
  from sketch, we can express the properties of Bareiss
*)
Lemma Bareiss_recE : forall m a (M: 'M[R]_(1 + m)),
    lreg a  ->
 (forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_m.+1), a ^+ k %| minor f1 f2 M) ->
 (forall p  (h h' :p.+1 <= 1 + m),
   lreg (minor (widen_ord h) (widen_ord h') M)) ->
    a ^+ m * (Bareiss_rec a M) = \det M.
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
set r := Bareiss_rec _ _ => hh.
have : a ^+ m.+1 *( d ^+m * r) =
       a ^+ m.+1 * \det (dvd_step a (d *: N - c *m l)) by rewrite hh.
rewrite det_dvd_step //; last by
  move => i j; apply (det_dvd_step_tool h2).
move => heq2.
have hX : lreg (M 0 0 ^+ (1 + m)) by apply/lregX.
apply/hX.
rewrite -{3}heq key_lemma -heq2 [M 0 0 ^+ (1 + m)]exprS -mulrA.
congr(_ * _).
by rewrite mulrCA.
Qed.

(*
  we start the algorithm with a = 1
*)
Definition Bareiss (n: nat) (M: 'M[R]_(1 + n)) :=
  Bareiss_rec 1 M.

Lemma BareissE : forall n (M: 'M[R]_(1 + n)),
 (forall p (h h': p.+1 <= 1 + n), lreg (pminor h h' M)) ->
  Bareiss M = \det M.
Proof.
rewrite /Bareiss => n M h.
have h1 : lreg (1: R) by apply/lreg1.
have h2 : forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_n.+1),
     1 ^+ k %| minor f1 f2 M.
- by move => k f1 f2; rewrite expr1n dvd1r.
move: (Bareiss_recE h1 h2 h).
by rewrite expr1n mul1r.
Qed.

End Bareiss2.


(*
  In practice, we apply this algorithm to the characteristic matrix
  so we get the characteristic polynomial in polynomial time
*)
Require Import polydvd.

Import PolyDvdRing.

Section Bareiss_det.
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
  Bareiss (char_poly_mx M).

(*
  Here is our alternative definition of char_poly
*)
Lemma char_poly_altE : forall n (M: 'M[R]_(1 + n)),
  char_poly_alt M = char_poly M.
Proof.
rewrite /char_poly_alt /char_poly => n M.
rewrite BareissE //.
move => p h h'; apply/monic_lreg.
apply pminor_char_poly_mx_monic.
Qed.

(* The actual determinant function based on Bareiss *)
Definition bdet n (M : 'M[R]_(1 + n)) := (char_poly_alt (-M))`_0.

Lemma bdetE : forall n (M : 'M[R]_(1 + n)), bdet M = \det M.
Proof.
move=> n M.
rewrite /bdet char_poly_altE char_poly_det.
have -> : - M = -1 *: M by apply/matrixP => i j; rewrite !mxE mulN1r.
by rewrite detZ mulrA -expr2 sqrr_sign mul1r.
Qed.

End Bareiss_det.

