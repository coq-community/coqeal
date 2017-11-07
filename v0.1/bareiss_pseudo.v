(* Version of Bareiss/Sasaki-Murao based on pseudo-division *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice.
Require Import matrix bigop zmodp mxalgebra poly polydiv mxpoly.

Require Import minor.

Import Pdiv.Ring Pdiv.RingComRreg Pdiv.RingMonic GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section prelude.

Variable R : ringType.

Let lreg := GRing.lreg.
Let rreg := GRing.rreg.

Lemma monic_lreg (p : {poly R}) : p \is monic -> lreg p.
Proof. by rewrite monicE=> /eqP h; apply/lreg_lead; rewrite h; apply/lreg1. Qed.

Lemma monic_rreg (p : {poly R}) : p \is monic -> rreg p.
Proof. by rewrite monicE=> /eqP h; apply/rreg_lead; rewrite h; apply/rreg1. Qed.

End prelude.

Section Bareiss1.

Variable R : comRingType.

Lemma L1 m a d (l : 'rV[R]_m) (c : 'cV[R]_m) (M : 'M[R]_m) : 
  \det (block_mx d%:M l (a *: c) (a *: M)) = a ^+ m * \det (block_mx d%:M l c M).
Proof.
have -> : block_mx d%:M l (a *: c) (a *: M) = 
          block_mx 1%:M 0 0 a%:M *m block_mx d%:M l c M
  by rewrite mulmx_block ?(mul0mx,mul1mx,addr0,add0r,mul_scalar_mx).
by rewrite det_mulmx det_ublock det1 mul1r det_scalar.

(* set X := block_mx d%:M l c M. *)
(* have huniq : uniq (map (lift 0) (enum 'I_m)). *)
(* - rewrite map_inj_in_uniq ?enum_uniq //. *)
(*   move => i j hi hj /=. *)
(*   by apply/lift_inj. *)
(* have htool : forall s, 0 \in (map (lift 0) s) -> False. *)
(* - move => n /=. *)
(*   by elim => [ | hd tl hi]. *)
(* have -> : block_mx d%:M l (a *: c) (a *: M) = *)
(*   foldl (fun N i => line_scale i a N) X (map (lift 0) (enum 'I_m)). *)
(* - apply/row_matrixP => i. *)
(*   case: (lines_scale_row a X huniq) => hl hr. *)
(*   move: (hl i) (hr i) => {hl hr}. *)
(*   case: (splitP i) => j. *)
(*   + rewrite [j]ord1 {j} => hi. *)
(*     have -> : i = 0 by apply/ord_inj. *)
(*     move => _ {hi} /= ->. *)
(*     * apply/rowP => j; rewrite !mxE. *)
(*       by case: splitP. *)
(*     by apply/negP/htool. *)
(*   move => hi. *)
(*   have -> : i = lift 0 j by apply/ord_inj. *)
(*   move => -> /=. *)
(*   + move => _. *)
(*     apply/rowP => k; rewrite !mxE. *)
(*     case: splitP => x; first by rewrite [x]ord1. *)
(*     rewrite !mxE => _. *)
(*     case: splitP => y; by rewrite !mxE. *)
(*   rewrite mem_map ?mem_enum //. *)
(*   by apply/lift_inj. *)
(* by rewrite det_lines_scale size_map size_enum_ord /=. *)
Qed.

(* Definition L3tool m (c: 'cV[R]_m) (d: R) (i: 'I_(1 + m)) := *)
(*   match split i with *)
(*     | inl _ => d *)
(*     | inr j => c j 0 *)
(*   end. *)

(* Lemma L3toolE0 m (c: 'cV[R]_m) d : L3tool c d 0 = d. *)
(* Proof. *)
(* rewrite /L3tool. *)
(* by case: splitP. *)
(* Qed. *)

(* Lemma L3toolES m (c: 'cV[R]_m) d (i: 'I_m) : L3tool c d (lift 0 i) = c i 0. *)
(* Proof. *)
(* rewrite /L3tool. *)
(* case: splitP => x /=; first by rewrite [x]ord1. *)
(* rewrite /bump leq0n => /eqP; rewrite eqSS => /eqP h. *)
(* by have -> : i = x by apply/ord_inj. *)
(* Qed. *)

Lemma L3 m (d: R) (l: 'rV[R]_m) (c c0: 'cV[R]_m) (M: 'M[R]_m):
  \det (block_mx d%:M l c M) =
  \det (block_mx d%:M l (c - d *: c0) (M - c0 *m l)).
Proof.
have -> : block_mx d%:M l (c - d *: c0) (M - c0 *m l) = 
          block_mx 1%:M 0 (- c0) 1%:M *m block_mx d%:M l c M
  by rewrite mulmx_block ?(mul0mx,mul1mx,addr0) mul_mx_scalar 
             [_ + c]addrC [_ + M]addrC scalerN mulNmx.
by rewrite det_mulmx det_lblock !det1 !mul1r.

(* pose X := block_mx d%:M l c M. *)
(* have huniq : uniq (map (lift 0) (enum 'I_m)). *)
(* - rewrite map_inj_in_uniq ?enum_uniq //. *)
(*   move => i j hi hj /=. *)
(*   by apply/lift_inj. *)
(* have htool : forall s, 0 \in (map (lift 0) s) -> False. *)
(* - move => n /=. *)
(*   by elim => [ | hd tl hi]. *)
(* have htool2 : 0 \notin (map (lift 0) (enum 'I_m)). *)
(* - by apply/negP/htool. *)
(* have -> : block_mx d%:M l (c -d *: c0) (M - c0 *m l) = *)
(*   foldl (fun N i => line_comb i 0 (-(L3tool c0 d i)) N) X *)
(*         (map (lift 0) (enum 'I_m)). *)
(* - apply/row_matrixP => i. *)
(*   case: (lines_comb_row_dep (fun i => - (L3tool c0 d i)) X huniq htool2) *)
(*      => hl hr. *)
(*   move: (hl i) (hr i) => {hl hr}. *)
(*   case: (splitP i) => j. *)
(*   + rewrite [j]ord1 {j} => hi. *)
(*     have -> : i = 0 by apply/ord_inj. *)
(*     move => _ {hi i} /= -> //. *)
(*     apply/rowP => j; rewrite !mxE. *)
(*     by case: splitP. *)
(*   move => hi. *)
(*   have -> : i = lift 0 j by apply/ord_inj. *)
(*   move => -> /= {i hi}. *)
(*   + rewrite L3toolES => _. *)
(*     apply/rowP => k; rewrite !mxE. *)
(*     case: splitP => x /= ; first by rewrite [x]ord1. *)
(*     rewrite /bump leq0n => /eqP; rewrite eqSS => /eqP hjx. *)
(*     have -> : j = x by apply/ord_inj. *)
(*     case: splitP => z // {j hjx}; rewrite [z]ord1 {z} !mxE => _. *)
(*     case: splitP => y; rewrite !mxE. *)
(*     * rewrite [y]ord1 {y} => _. *)
(*       by rewrite mulrC mulr1n mulNr. *)
(*     by move => _; rewrite big_ord_recl big_ord0 addr0 mulNr. *)
(*   rewrite mem_map ?mem_enum //. *)
(*   by apply/lift_inj. *)
(* by rewrite det_lines_comb_dep // size_map size_enum_ord /=. *)
Qed.

Lemma key_lemma m d (l : 'rV[R]_m) (c : 'cV[R]_m) M :
  d ^+ m * \det (block_mx d%:M l c M) = d * \det (d *: M - c *m l).
Proof.
(* L1 inlined: *)
(* rewrite -[d ^+ m]mul1r -det_scalar -(det1 _ 1) -(det_ublock _ 0) -det_mulmx. *)
(* rewrite mulmx_block ?(mul0mx,addr0,add0r,mul1mx,mul_scalar_mx). *)
rewrite -L1.
by rewrite (L3 d l (d *: c) c (d *: M)) subrr det_ublock det_scalar1.
Qed.

(*
  The key lemma of our proof: after simplification,
  all the p-minors (involving 1st line/column)
  can be divided by (M 0 0)^p-1
*)

Lemma key_lemma_sub m n k d (l : 'rV[R]_n) (c : 'cV[R]_m) (M : 'M[R]_(m,n))
  (f1 : 'I_k -> 'I_m) (f2 : 'I_k -> 'I_n):
  d * (minor f1 f2 (d *: M - c *m l)) =
  d ^+ k * (minor (lift_pred f1) (lift_pred f2) (block_mx d%:M l c M)).
Proof.
rewrite /minor submatrix_lift_block key_lemma submatrix_add submatrix_scale.
by rewrite submatrix_opp submatrix_mul.
Qed.

Lemma blockE00 m n d (l : 'rV[R]_n) (c : 'cV[R]_m) (M : 'M[R]_(m,n)):
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

End Bareiss1.

Section Bareiss2.
Variable R: comRingType.

Definition dvd_step (m n:nat) (d: {poly R}) (M: 'M[{poly R}]_(m,n)) :
  'M[{poly R}]_(m,n) := map_mx (fun x => rdivp x d) M.

(*
  determinant equality for division step
*)
Lemma det_dvd_step: forall n a (M: 'M[{poly R}]_n),
  a \is monic ->
  (forall i j, rdvdp a (M i j)) ->
  a^+n * \det (dvd_step a M) = \det M.
Proof.
rewrite /dvd_step => n a M ha hj.
rewrite -detZ; f_equal.
by apply/matrixP => i j; rewrite !mxE mulrC rdivpK // (eqP ha) expr1n mulr1.
Qed.

Lemma det_dvd_step_tool : forall m n a (M N: 'M[{poly R}]_(m,n)),
  a \is monic -> M = a *: N -> forall i j, rdvdp a (M i j).
Proof.
move => m n a M N ha /matrixP h i j.
by rewrite (h i j) !mxE mulrC rdvdp_mull.
Qed.

Let lreg := GRing.lreg.

Lemma sketch m n (a d: {poly R}) (l: 'rV[{poly R}]_n)
               (c: 'cV[{poly R}]_m) (M: 'M[{poly R}]_(m,n)):
 a \is monic ->
 (forall (k:nat) (f1: 'I_k.+1 -> 'I_(1 + m)) (f2: 'I_k.+1 -> 'I_(1 + n)),
     rdvdp (a ^+ k) (minor f1 f2 (block_mx d%:M l c M))) ->
 (forall p (h: p.+1 <= 1 + m) (h': p.+1 <= 1 + n),
   pminor h h' (block_mx d%:M l c M) \is monic) ->
   let M' := d *: M - c *m l in
   let M'':= dvd_step a M' in
     [/\ d \is monic,
       (forall k (f1: 'I_k.+1 -> 'I_m) (f2: 'I_k.+1 -> 'I_n),
         rdvdp (d ^+ k) (minor f1 f2 M'')),
       M' = a *: M'' &
  (forall p (h: p.+1 <= m) (h': p.+1 <= n),
   pminor h h' M'' \is monic)].
Proof.
rewrite /pminor => ha hM hN.
set M0 := block_mx d%:M l c M.
(* d is the 1x1 principal minor of M0 *)
have hh : d = minor (step_fun (ltn0Sn _)) (step_fun (ltn0Sn _)) M0.
- rewrite (@minor_eq _ _ _ _ _ (fun _ => 0) _ (fun _ => 0)) ?minor1 //.
  + by rewrite /M0 blockE00.
  + by move => x; rewrite step0.
  by move => x; rewrite step0.
(* all principal minors of M0 are monic, so M 0 0 is *)
have h2 : d \is monic.
- by rewrite hh /M0; apply hN.
set M' := d *: M - c *m l.
set M'' := dvd_step a M'.
set f : forall m, 'I_m -> 'I_2 -> 'I_(1 + m) :=
  fun m (i: 'I_m) (x: 'I_2) => if x == 0 then 0 else (lift 0 i).
(*
  all elements of M' can be expressed as 2x2 minors of M,
  so a divide all these
*)
have h4 : forall i j, rdvdp a (M' i j).
- move => i j; rewrite /M' !mxE big_ord_recl big_ord0 addr0.
  move: (hM 1%nat (f _ i) (f _ j)).
  by rewrite !minor2 /f /= expr1 blockE00 blockEi0 blockE0i blockEij.
(*
  since a divides all M' i j, all the divisions are exact,
  and thus M' = a * M''
*)
have h6 : forall i j, M' i j = a * M'' i j.
  move => i j; rewrite [(dvd_step _ _) i j]mxE.
  have hcomm : GRing.comm a (lead_coef a)%:P by rewrite /GRing.comm mulrC.
  by rewrite mulrC rdivpK // (eqP ha) expr1n mulr1.
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
- by move => k; apply/lregX/monic_lreg.
have h9 : forall k, d ^+ k \is monic by move => k; by apply/monic_exp.
have h9': forall k, (lead_coef (d ^+ k))%:P = 1
 by move => k; rewrite (eqP (h9 k)).
have h10 : forall k (f1: 'I_k.+1 -> 'I_m) (f2: 'I_k.+1 -> 'I_n),
  rdvdp (d ^+ k) (minor f1 f2 M'').
- move => k f1 f2.
  have : d * a ^+ k.+1 * minor f1 f2 M'' =
    d ^+ k.+1 * minor (lift_pred f1) (lift_pred f2) M0
  by rewrite -h8 -mulrA -h7.
  case/rdvdpP : (hM _ (lift_pred f1) (lift_pred f2));
    first by apply/monic_exp.
  move => pM -> h.
  apply/rdvdpP => //; exists pM.
  apply/(ak k.+1)/(monic_lreg h2).
  rewrite mulrA h exprS -mulrA.
  congr (_ * _).
  rewrite mulrA mulrC.
  congr (_ * _).
  by rewrite mulrC.
split.
- exact : h2.
- exact : h10.
- exact : h6'.
rewrite -/M'' => p h h'.
rewrite -(@monicMl _ (a ^+ p.+1)); last by apply/monic_exp.
rewrite -h7 -(@monicMl _ d) // h8 monicMr; first by apply/monic_exp.
rewrite (@minor_eq _ _ _ _ _ (step_fun (size_tool h)) _
                             (step_fun (size_tool h'))) ?hN //.
- by move => x; rewrite lift_pred_step.
by  move => x; rewrite lift_pred_step.
Qed.

(*
  formal definition of Bareiss algorithm
*)
Fixpoint Bareiss_rec m a : 'M[{poly R}]_(1 + m) -> {poly R} :=
  match m return 'M[_]_(1 + m) -> {poly R} with
    | S p => fun (M: 'M[_]_(1 + _)) =>
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
Lemma Bareiss_recE : forall m a (M: 'M[{poly R}]_(1 + m)),
   a \is monic  ->
 (forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_m.+1),
    rdvdp (a ^+ k) (minor f1 f2 M)) ->
 (forall p  (h h' :p.+1 <= 1 + m),
 (minor (step_fun h) (step_fun h') M) \is monic) ->
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
case: (@sketch _ _ a (M 0 0) (ursubmx M) (dlsubmx M) (drsubmx M) ha hM hm)
 => hM00 h1 h2 h3.
move: (hi d (dvd_step a (d *: N - c *m l)) hM00 h1 h3).
set r := Bareiss_rec _ _ => hh.
have : a ^+ m.+1 *( d ^+m * r) =
       a ^+ m.+1 * \det (dvd_step a (d *: N - c *m l)) by rewrite hh.
rewrite det_dvd_step //; last by
  move => i j; apply (det_dvd_step_tool ha h2).
move => heq2.
have hX : M 0 0 ^+ (1 + m) \is monic by apply/monic_exp.
apply/(monic_lreg hX).
rewrite -{3}heq key_lemma -heq2 [M 0 0 ^+ (1 + m)]exprS -mulrA.
congr(_ * _).
by rewrite mulrCA.
Qed.

(*
  we start the algorithm with a = 1
*)
Definition Bareiss (n: nat) (M: 'M[{poly R}]_(1 + n)) :=
  Bareiss_rec 1 M.

Lemma BareissE : forall n (M: 'M[{poly R}]_(1 + n)),
 (forall p (h h': p.+1 <= 1 + n), pminor h h' M \is monic) ->
  Bareiss M = \det M.
Proof.
rewrite /Bareiss => n M h.
have h1 : (1: {poly R}) \is monic by apply/monic1.
have h2 : forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_n.+1),
     rdvdp (1 ^+ k) (minor f1 f2 M)
 by move => k f1 f2; rewrite expr1n rdvd1p.
move: (Bareiss_recE h1 h2 h).
by rewrite expr1n mul1r.
Qed.

(*
  all principal minor of the characteristic matrix are monic
*)
Lemma pminor_char_poly_mx_monic: forall m p (M: 'M[R]_m) (h h': p.+1 <= m),
  pminor h h' (char_poly_mx M) \is monic.
Proof.
rewrite /pminor => m p M h h'.
rewrite (@minor_eq _ _ _ _ _ (step_fun h) _ (step_fun h)); last first.
- by apply: step_fun_eq.
- by move => x.
rewrite /minor submatrix_char_poly_mx; last by apply inj_step.
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
move => p h h'.
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

End Bareiss2.


(* Executable version *)

Require Import cssralg Matrix cseqpoly.

Section exBareiss.

Variable R : comRingType.
Variable CR: cringType R.

Definition cpoly := seq_cringType CR.

Definition ex_dvd_step d (M : Matrix cpoly) :=
 mapM (fun x => divp_seq x d) M.

Lemma ex_dvd_stepE (m n: nat) (d: {poly R}) (M: 'M[{poly R}]_(m,n)):
 trans (dvd_step d M) = ex_dvd_step (trans d) (trans M).
Proof.
rewrite /dvd_step /ex_dvd_step.
case : m n M => [ | m] [ | n].
  by move=> M; rewrite [M]thinmx0.
  by move=> M; rewrite [M]flatmx0.
  by move=> M; rewrite [M]thinmx0.
rewrite [m.+1]/(1 + m)%N [n.+1]/(1 + n)%N => M.
rewrite -[M]submxK /trans /= !mxE -map_ursubmx -map_dlsubmx -map_drsubmx
   block_mxKur block_mxKdl !block_mxKdr.
case: splitP => x // _; rewrite [x]ord1 !mxE; clear x.
case: splitP => x // _; rewrite [x]ord1 !mxE !lshift0; clear x.
set f := fun x => divp_seq x (trans d).
set g := fun x => rdivp x d.
have h : forall a, trans (g a) = f (trans a)
  by rewrite /f /g => a; rewrite -divp_seqE.
by rewrite -divp_seqE (rV2seq_map h) (cV2seq_map h) (mat2Matrix_map h).
Qed.

Fixpoint exBareiss_rec n g (M: Matrix cpoly) := match n,M with
  | _,eM => g
  | O,_ => g
  | S p, cM a l c M =>
    let M' := subM (multEM a M) (mults c l) in
    let M'' := ex_dvd_step g M' in
      exBareiss_rec p a M''
end.

Lemma exBareiss_rec_unfold : forall n g a l c M,
  exBareiss_rec (1 + n) g (cM a l c M) =
    exBareiss_rec n a (ex_dvd_step g (subM (multEM a M) (mults c l))).
Proof. by []. Qed.

Lemma exBareiss_recE : forall n (g: {poly R}) (M: 'M[{poly R}]_(1 + n)),
  trans (Bareiss_rec g M) =
    exBareiss_rec (1+n) (trans g) (trans M).
Proof.
elim => [ /= g M | n hi g]  //.
- by rewrite [dlsubmx M]flatmx0 [ursubmx M]thinmx0 cV2seq0 rV2seq0 /=.
rewrite [n.+1]/(1 + n)%nat  => M.
rewrite -{2}[M]submxK [ulsubmx M]mx11_scalar !mxE lshift0
        block_mxE exBareiss_rec_unfold.
rewrite [Bareiss_rec _ _]/= hi.
rewrite (@map_mxE _ _ _ _ _ (fun x : seq CR => divp_seq x (trans g)))
 ?subE ?multEME ?multsE // => a.
by rewrite -divp_seqE.
Qed.

Notation "'1'" := (one cpoly).

Definition exBareiss n (M: Matrix cpoly) := exBareiss_rec n 1 M.

Lemma exBareissE : forall n (M: 'M[{poly R}]_(1 + n)),
  trans (Bareiss M) = exBareiss (1 + n) (trans M).
Proof.
rewrite /Bareiss /exBareiss => n M.
by rewrite exBareiss_recE oneE.
Qed.

Notation "'\X'" := (indet _ 1).

Definition ex_char_poly_mx n (M : Matrix CR) :=
 subM (multEM \X (ident _ n)) (mapM (@polyC_seq _ CR) M).

Lemma ex_char_poly_mxE : forall n (M: 'M[R]_n),
  trans (char_poly_mx M) = ex_char_poly_mx n (trans M).
Proof.
rewrite /ex_char_poly_mx /char_poly_mx => n M.
rewrite subE -scalemx1 multEME idmxE -indetE expr1
  (@map_mxE _ _ _ _ _  (@polyC_seq R CR)) // => a.
by rewrite -polyC_seqE.
Qed.

End exBareiss.

Section exDet.

Variable R : comRingType.
Variable CR: cringType R.

Definition ex_char_poly_alt n (M : Matrix CR) :=
  exBareiss n (ex_char_poly_mx n M).

Lemma ex_char_polyE : forall n (M: 'M[R]_(1 + n)),
  trans (char_poly_alt M) = ex_char_poly_alt (1 + n) (trans M).
Proof.
rewrite /char_poly_alt /ex_char_poly_alt => n M.
by rewrite -ex_char_poly_mxE -exBareissE.
Qed.

Definition ex_bdet n (M : Matrix CR) :=
  nth (zero CR) (ex_char_poly_alt n (oppM M)) 0.

Lemma ex_detE : forall n (M : 'M[R]_(1 + n)),
  trans (bdet M) = ex_bdet (1 + n) (trans M).
Proof.
rewrite /ex_bdet /bdet => n M.
rewrite -oppME -ex_char_polyE -[zero CR]zeroE.
by case: char_poly_alt => [[]].
Qed.

End exDet.

(* Extraction Language Haskell. *)
(*  Extraction "Bareiss" ex_bdet. *)
