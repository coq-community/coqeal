Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path ssralg.
Require Import fintype perm choice matrix bigop zmodp poly polydiv mxpoly.

Require Import minor.

Import Pdiv.Ring Pdiv.RingComRreg Pdiv.RingMonic GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Open Scope ring_scope.

Section prelude.

Variable R : ringType.

Let lreg := GRing.lreg.
Let rreg := GRing.rreg.

Lemma monic_lreg (p : {poly R}) : p \is monic -> lreg p.
Proof. by rewrite monicE=> /eqP h; apply/lreg_lead; rewrite h; apply/lreg1. Qed.

Lemma monic_rreg (p : {poly R}) : p \is monic -> rreg p.
Proof. by rewrite monicE=> /eqP h; apply/rreg_lead; rewrite h; apply/rreg1. Qed.

End prelude.

Section bareiss_def.

Variable R : comRingType.

Definition dvd_step m n (d : {poly R}) (M : 'M[{poly R}]_(m,n)) :
  'M[{poly R}]_(m,n) := map_mx (fun x => rdivp x d) M.

(* formal definition of Bareiss algorithm *)
Fixpoint bareiss_rec m a : 'M[{poly R}]_(1 + m) -> {poly R} :=
  match m return 'M[_]_(1 + m) -> {poly R} with
    | S p => fun (M: 'M[_]_(1 + _)) =>
      let d   := M 0 0 in
      let l   := ursubmx M in
      let c   := dlsubmx M in
      let N   := drsubmx M in
      let M'  := d *: N - c *m l in
      let M'' := dvd_step a M' in
        bareiss_rec d M''
    | _ => fun M => M 0 0
  end.

Definition bareiss n (M : 'M[{poly R}]_(1 + n)) := bareiss_rec 1 M.

Definition bareiss_char_poly n (M : 'M[R]_(1 + n)) := bareiss (char_poly_mx M).

(* The actual determinant function based on Bareiss *)
Definition bdet n (M : 'M[R]_(1 + n)) := (bareiss_char_poly (-M))`_0.

End bareiss_def.

Section bareiss_correctness.

(* First prove some lemmas for an arbitrary comRingType *)
Section bareiss_comRingType.

Variable R : comRingType.

(* TODO: inline this into key_lemma *)
Lemma help m d (l : 'rV[R]_m) (c c0 : 'cV[R]_m) (M : 'M[R]_m):
  \det (block_mx d%:M l c M) =
  \det (block_mx d%:M l (c - d *: c0) (M - c0 *m l)).
Proof.
have -> : block_mx d%:M l (c - d *: c0) (M - c0 *m l) = 
          block_mx 1%:M 0 (- c0) 1%:M *m block_mx d%:M l c M
  by rewrite mulmx_block ?(mul0mx,mul1mx,addr0) mul_mx_scalar 
             [_ + c]addrC [_ + M]addrC scalerN mulNmx.
by rewrite det_mulmx det_lblock !det1 !mul1r.
Qed.

Lemma key_lemma m d (l : 'rV[R]_m) (c : 'cV[R]_m) M :
  d ^+ m * \det (block_mx d%:M l c M) = d * \det (d *: M - c *m l).
Proof.
rewrite -[d ^+ m]mul1r -det_scalar -(det1 _ 1) -(det_ublock _ 0) -det_mulmx.
rewrite mulmx_block ?(mul0mx,addr0,add0r,mul1mx,mul_scalar_mx).
by rewrite (help d l (d *: c) c (d *: M)) subrr det_ublock det_scalar1.
Qed.

(* The key lemma of our proof: after simplification, all the p-minors (involving *)
(* 1st line/column) can be divided by (M 0 0)^p-1 *)
Lemma key_lemma_sub m n k d (l : 'rV[R]_n) (c : 'cV[R]_m) (M : 'M[R]_(m,n))
  (f : 'I_k -> 'I_m) (g : 'I_k -> 'I_n) :
  d * (minor f g (d *: M - c *m l)) =
  d ^+ k * (minor (lift_pred f) (lift_pred g) (block_mx d%:M l c M)).
Proof.
rewrite /minor submatrix_lift_block key_lemma submatrix_add submatrix_scale.
by rewrite submatrix_opp submatrix_mul.
Qed.

(* General lemmas about accessing into block_mx *)
Lemma blockE00 m n d (l : 'rV[R]_n) (c : 'cV[R]_m) (M : 'M[R]_(m,n)):
  (block_mx d%:M l c M) 0 0 = d.
Proof. by do ?rewrite (mxE,split1,unlift_none) /=; rewrite mulr1n. Qed.

Lemma blockE0i m n d (l : 'rV[R]_n) (c : 'cV[R]_m) (M : 'M[R]_(m,n)) i :
  (block_mx d%:M l c M) 0 (lift 0 i) = (l 0 i).
Proof. by rewrite mxE split1 unlift_none /= mxE split1 liftK. Qed.

Lemma blockEi0 m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)) i:
  (block_mx d%:M l c M) (lift 0 i) 0 = (c i 0).
Proof. by rewrite mxE split1 liftK /= mxE split1 unlift_none. Qed.

Lemma blockEij m n d (l: 'rV[R]_n) (c: 'cV[R]_m) (M: 'M[R]_(m,n)) i j:
  (block_mx d%:M l c M) (lift 0 i) (lift 0 j) = (M i j).
Proof. by do? rewrite mxE split1 liftK /=. Qed.

End bareiss_comRingType.

(* Switch to polynomials over a commutative ring *)
Section bareiss_poly.

Variable R : comRingType.

(* determinant equality for division step *)
Lemma det_dvd_step n a (M : 'M[{poly R}]_n) (ha : a \is monic) 
  (hj : forall i j, rdvdp a (M i j)) :
  a^+n * \det (dvd_step a M) = \det M.
Proof.
rewrite /dvd_step -detZ; congr (\det _).
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
have hh : d = minor (widen_ord (ltn0Sn _)) (widen_ord (ltn0Sn _)) M0.
  rewrite (@minor_eq _ _ _ _ _ (fun _ => 0) _ (fun _ => 0)) ?minor1 //.
    by rewrite /M0 blockE00.
    by move => x; apply/ord_inj; rewrite [x]ord1. 
  by move => x; apply/ord_inj; rewrite [x]ord1. 
(* all principal minors of M0 are monic, so M 0 0 is *)
have h2 : d \is monic by rewrite hh /M0; apply hN.
set M' := d *: M - c *m l.
set M'' := dvd_step a M'.
set f : forall m, 'I_m -> 'I_2 -> 'I_(1 + m) :=
  fun m (i: 'I_m) (x: 'I_2) => if x == 0 then 0 else (lift 0 i).
(*
  all elements of M' can be expressed as 2x2 minors of M,
  so a divide all these
*)
have h4 : forall i j, rdvdp a (M' i j).
  move => i j; rewrite /M' !mxE big_ord_recl big_ord0 addr0.
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
  move => k f1 f2.
  by rewrite h6' /minor submatrix_scale detZ.
(*
  using all theses, we can now prove our goals
*)
have h8: forall k (f1: 'I_k -> 'I_m) (f2: 'I_k -> 'I_n),
  d * minor f1 f2 M' =
    d ^+ k * minor (lift_pred f1) (lift_pred f2) M0.
  move => k f1 f2.
  by rewrite /M0 /M' key_lemma_sub.
have ak : forall k, lreg (a^+k) by move => k; apply/lregX/monic_lreg.
have h9 : forall k, d ^+ k \is monic by move => k; by apply/monic_exp.
have h9': forall k, (lead_coef (d ^+ k))%:P = 1
 by move => k; rewrite (eqP (h9 k)).
have h10 : forall k (f1: 'I_k.+1 -> 'I_m) (f2: 'I_k.+1 -> 'I_n),
  rdvdp (d ^+ k) (minor f1 f2 M'').
  move => k f1 f2.
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
by rewrite (@minor_eq _ _ _ _ _ (widen_ord (size_tool h)) _
                                (widen_ord (size_tool h'))) ?hN // => x;
   rewrite lift_pred_widen_ord.
Qed.

(* from sketch, we can express the properties of Bareiss *)
Lemma bareiss_recE : forall m a (M : 'M[{poly R}]_(1 + m)),
   a \is monic  ->
 (forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_m.+1),
    rdvdp (a ^+ k) (minor f1 f2 M)) ->
 (forall p  (h h' :p.+1 <= 1 + m),
 (minor (widen_ord h) (widen_ord h') M) \is monic) ->
    a ^+ m * (bareiss_rec a M) = \det M.
Proof.
elim => [ | m hi] //=.
  move => a M ha h1 h2.
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
set r := bareiss_rec _ _ => hh.
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

Lemma bareissE : forall n (M : 'M[{poly R}]_(1 + n)),
 (forall p (h h': p.+1 <= 1 + n), pminor h h' M \is monic) ->
  bareiss M = \det M.
Proof.
rewrite /bareiss => n M h.
have h1 : (1: {poly R}) \is monic by apply/monic1.
have h2 : forall (k:nat) (f1 f2: 'I_k.+1 -> 'I_n.+1),
     rdvdp (1 ^+ k) (minor f1 f2 M)
 by move => k f1 f2; rewrite expr1n rdvd1p.
move: (bareiss_recE h1 h2 h).
by rewrite expr1n mul1r.
Qed.

Lemma bareiss_char_polyE n (M : 'M[R]_(1 + n)) :
  bareiss_char_poly M = char_poly M.
Proof.
rewrite /bareiss_char_poly /char_poly bareissE // => p h h'.
exact: pminor_char_poly_mx_monic.
Qed.

Lemma bdetE n (M : 'M[R]_(1 + n)) : bdet M = \det M.
Proof.
rewrite /bdet bareiss_char_polyE char_poly_det.
have -> : - M = -1 *: M by apply/matrixP => i j; rewrite !mxE mulN1r.
by rewrite detZ mulrA -expr2 sqrr_sign mul1r.
Qed.

End bareiss_poly.
End bareiss_correctness.


(* Executable version *)

(* Require Import cssralg cMatrix cseqpoly. *)

(* Section exBareiss. *)

(* Variable R : comRingType. *)
(* Variable CR: cringType R. *)

(* Definition cpoly := seq_cringType CR. *)

(* Definition ex_dvd_step d (M : Matrix cpoly) := *)
(*  mapM (fun x => divp_seq x d) M. *)

(* Lemma ex_dvd_stepE (m n: nat) (d: {poly R}) (M: 'M[{poly R}]_(m,n)): *)
(*  trans (dvd_step d M) = ex_dvd_step (trans d) (trans M). *)
(* Proof. *)
(* rewrite /dvd_step /ex_dvd_step. *)
(* case : m n M => [ | m] [ | n]. *)
(*   by move=> M; rewrite [M]thinmx0. *)
(*   by move=> M; rewrite [M]flatmx0. *)
(*   by move=> M; rewrite [M]thinmx0. *)
(* rewrite [m.+1]/(1 + m)%N [n.+1]/(1 + n)%N => M. *)
(* rewrite -[M]submxK /trans /= !mxE -map_ursubmx -map_dlsubmx -map_drsubmx *)
(*    block_mxKur block_mxKdl !block_mxKdr. *)
(* case: splitP => x // _; rewrite [x]ord1 !mxE; clear x. *)
(* case: splitP => x // _; rewrite [x]ord1 !mxE !lshift0; clear x. *)
(* set f := fun x => divp_seq x (trans d). *)
(* set g := fun x => rdivp x d. *)
(* have h : forall a, trans (g a) = f (trans a) *)
(*   by rewrite /f /g => a; rewrite -divp_seqE. *)
(* by rewrite -divp_seqE (rV2seq_map h) (cV2seq_map h) (mat2Matrix_map h). *)
(* Qed. *)

(* Fixpoint exBareiss_rec n g (M: Matrix cpoly) := match n,M with *)
(*   | _,eM => g *)
(*   | O,_ => g *)
(*   | S p, cM a l c M => *)
(*     let M' := subM (multEM a M) (mults c l) in *)
(*     let M'' := ex_dvd_step g M' in *)
(*       exBareiss_rec p a M'' *)
(* end. *)

(* Lemma exBareiss_rec_unfold : forall n g a l c M, *)
(*   exBareiss_rec (1 + n) g (cM a l c M) = *)
(*     exBareiss_rec n a (ex_dvd_step g (subM (multEM a M) (mults c l))). *)
(* Proof. by []. Qed. *)

(* Lemma exBareiss_recE : forall n (g: {poly R}) (M: 'M[{poly R}]_(1 + n)), *)
(*   trans (Bareiss_rec g M) = *)
(*     exBareiss_rec (1+n) (trans g) (trans M). *)
(* Proof. *)
(* elim => [ /= g M | n hi g]  //. *)
(* - by rewrite [dlsubmx M]flatmx0 [ursubmx M]thinmx0 cV2seq0 rV2seq0 /=. *)
(* rewrite [n.+1]/(1 + n)%nat  => M. *)
(* rewrite -{2}[M]submxK [ulsubmx M]mx11_scalar !mxE lshift0 *)
(*         block_mxE exBareiss_rec_unfold. *)
(* rewrite [Bareiss_rec _ _]/= hi. *)
(* rewrite (@map_mxE _ _ _ _ _ (fun x : seq CR => divp_seq x (trans g))) *)
(*  ?subE ?multEME ?multsE // => a. *)
(* by rewrite -divp_seqE. *)
(* Qed. *)

(* Notation "'1'" := (one cpoly). *)

(* Definition exBareiss n (M: Matrix cpoly) := exBareiss_rec n 1 M. *)

(* Lemma exBareissE : forall n (M: 'M[{poly R}]_(1 + n)), *)
(*   trans (Bareiss M) = exBareiss (1 + n) (trans M). *)
(* Proof. *)
(* rewrite /Bareiss /exBareiss => n M. *)
(* by rewrite exBareiss_recE oneE. *)
(* Qed. *)

(* Notation "'\X'" := (indet _ 1). *)

(* Definition ex_char_poly_mx n (M : Matrix CR) := *)
(*  subM (multEM \X (ident _ n)) (mapM (@polyC_seq _ CR) M). *)

(* Lemma ex_char_poly_mxE : forall n (M: 'M[R]_n), *)
(*   trans (char_poly_mx M) = ex_char_poly_mx n (trans M). *)
(* Proof. *)
(* rewrite /ex_char_poly_mx /char_poly_mx => n M. *)
(* rewrite subE -scalemx1 multEME idmxE -indetE expr1 *)
(*   (@map_mxE _ _ _ _ _  (@polyC_seq R CR)) // => a. *)
(* by rewrite -polyC_seqE. *)
(* Qed. *)

(* End exBareiss. *)

(* Section exDet. *)

(* Variable R : comRingType. *)
(* Variable CR: cringType R. *)

(* Definition ex_char_poly_alt n (M : Matrix CR) := *)
(*   exBareiss n (ex_char_poly_mx n M). *)

(* Lemma ex_char_polyE : forall n (M: 'M[R]_(1 + n)), *)
(*   trans (char_poly_alt M) = ex_char_poly_alt (1 + n) (trans M). *)
(* Proof. *)
(* rewrite /char_poly_alt /ex_char_poly_alt => n M. *)
(* by rewrite -ex_char_poly_mxE -exBareissE. *)
(* Qed. *)

(* Definition ex_bdet n (M : Matrix CR) := *)
(*   nth (zero CR) (ex_char_poly_alt n (oppM M)) 0. *)

(* Lemma ex_detE : forall n (M : 'M[R]_(1 + n)), *)
(*   trans (bdet M) = ex_bdet (1 + n) (trans M). *)
(* Proof. *)
(* rewrite /ex_bdet /bdet => n M. *)
(* rewrite -oppME -ex_char_polyE -[zero CR]zeroE. *)
(* by case: char_poly_alt => [[]]. *)
(* Qed. *)

(* End exDet. *)


(* (* Test computations *) *)

(* (* *)
(*    WARNING never use compute, but vm_compute, *)
(*    otherwise it's painfully slow *)
(* *) *)
(* Require Import ZArith Zinfra. *)
(* Section test. *)

(* Definition excp n (M: Matrix [cringType Z of Z]) := ex_char_poly_mx n M. *)

(* Definition idZ n := @ident _ [cringType Z of Z] n. *)

(* Definition cpmxid2 := (excp 2 (idZ 2)). *)
(* Definition cpid2 := (exBareiss_rec 2 [:: 1%Z] cpmxid2). *)

(* Eval vm_compute in cpid2. *)

(* Definition detid2 := horner_seq cpid2 0%Z. *)

(* Eval vm_compute in detid2. *)

(* Definition M2 := cM 19%Z [:: 3%Z] [:: (-2)%Z] (cM 26%Z [::] [::] (@eM _ _)). *)

(* Definition cpmxM2 := excp 2 M2. *)
(* Definition cpM2 := exBareiss 2 cpmxM2. *)

(* Eval vm_compute in cpM2. *)
(* Eval vm_compute in ex_bdet 2 M2. *)

(* (* Random 3x3 matrix *) *)
(* Definition M3 := *)
(*   cM 10%Z [:: (-42%Z); 13%Z] [:: (-34)%Z; 77%Z] *)
(*      (cM 15%Z [:: 76%Z] [:: 98%Z] *)
(*          (cM 49%Z [::] [::] (@eM _ _))). *)

(* Time Eval vm_compute in ex_bdet 3 M3. *)

(* (* Random 10x10 matrix *) *)
(* Definition M10 := cM (-7)%Z [:: (-12)%Z ; (-15)%Z ; (-1)%Z ; (-8)%Z ; (-8)%Z ; 19%Z ; (-3)%Z ; (-8)%Z ; 20%Z] [:: 5%Z ; (-14)%Z ; (-12)%Z ; 19%Z ; 20%Z ; (-5)%Z ; (-3)%Z ; 8%Z ; 16%Z] (cM 1%Z [:: 16%Z ; (-18)%Z ; 8%Z ; (-13)%Z ; 18%Z ; (-6)%Z ; 10%Z ; 6%Z] [:: 5%Z ; 4%Z ; 0%Z ; 4%Z ; (-18)%Z ; (-19)%Z ; (-2)%Z ; 3%Z] (cM (-8)%Z [:: 1%Z ; (-10)%Z ; 12%Z ; 0%Z ; (-14)%Z ; 18%Z ; (-5)%Z] [:: (-14)%Z ; (-10)%Z ; 15%Z ; 0%Z ; 13%Z ; (-12)%Z ; (-16)%Z] (cM (-13)%Z [:: (-2)%Z ; (-14)%Z ; (-11)%Z ; 15%Z ; (-1)%Z ; 8%Z] [:: 6%Z ; 9%Z ; (-19)%Z ; (-19)%Z ; (-16)%Z ; (-10)%Z] (cM (-12)%Z [:: 1%Z ; (-5)%Z ; 16%Z ; 5%Z ; 6%Z] [:: 16%Z ; (-20)%Z ; 19%Z ; 16%Z ; 5%Z] (cM 2%Z [:: (-10)%Z ; (-3)%Z ; (-17)%Z ; 18%Z] [:: 4%Z ; (-4)%Z ; 20%Z ; (-7)%Z] (cM 4%Z [:: (-8)%Z ; 2%Z ; 9%Z] [:: 17%Z ; 10%Z ; 10%Z] (cM (-15)%Z [:: 16%Z ; 3%Z] [:: 5%Z ; (-1)%Z] (cM 3%Z [:: 4%Z] [:: (-12)%Z] ((@eM _ _)))))))))). *)

(* Time Eval vm_compute in ex_bdet 10 M10. *)

(* (* *)
(* (* Random 20x20 matrix *) *)
(* Definition M20 := cM (-17)%Z [:: 4%Z ; 9%Z ; 4%Z ; (-7)%Z ; (-4)%Z ; 16%Z ; (-13)%Z ; (-6)%Z ; (-4)%Z ; (-9)%Z ; 18%Z ; 7%Z ; 3%Z ; (-14)%Z ; 8%Z ; (-17)%Z ; 17%Z ; (-2)%Z ; 8%Z] [:: 0%Z ; 10%Z ; 17%Z ; (-7)%Z ; 3%Z ; 18%Z ; (-3)%Z ; 6%Z ; 2%Z ; (-7)%Z ; (-3)%Z ; 16%Z ; 7%Z ; (-9)%Z ; 15%Z ; (-17)%Z ; (-9)%Z ; (-18)%Z ; 9%Z] (cM 13%Z [:: (-3)%Z ; 9%Z ; 7%Z ; 4%Z ; 18%Z ; 2%Z ; 7%Z ; 9%Z ; (-10)%Z ; 18%Z ; 4%Z ; 13%Z ; (-16)%Z ; (-5)%Z ; 6%Z ; (-14)%Z ; 3%Z ; 12%Z] [:: 14%Z ; (-15)%Z ; 14%Z ; (-7)%Z ; 11%Z ; 10%Z ; (-10)%Z ; 9%Z ; (-4)%Z ; (-7)%Z ; (-4)%Z ; 7%Z ; (-10)%Z ; 15%Z ; (-4)%Z ; 12%Z ; (-18)%Z ; 4%Z] (cM 16%Z [:: (-5)%Z ; 8%Z ; 4%Z ; 8%Z ; 4%Z ; (-18)%Z ; 10%Z ; 3%Z ; (-12)%Z ; 12%Z ; 8%Z ; 11%Z ; (-12)%Z ; (-1)%Z ; 12%Z ; (-5)%Z ; (-10)%Z] [:: 1%Z ; (-15)%Z ; (-3)%Z ; (-3)%Z ; 6%Z ; (-3)%Z ; 18%Z ; 6%Z ; (-6)%Z ; (-10)%Z ; 15%Z ; 11%Z ; 6%Z ; (-4)%Z ; (-4)%Z ; 9%Z ; (-3)%Z] (cM (-12)%Z [:: 1%Z ; 6%Z ; 7%Z ; 5%Z ; 0%Z ; (-2)%Z ; 2%Z ; 14%Z ; 15%Z ; (-10)%Z ; (-14)%Z ; (-6)%Z ; 3%Z ; 17%Z ; (-11)%Z ; (-8)%Z] [:: (-15)%Z ; (-8)%Z ; 5%Z ; 18%Z ; 15%Z ; (-14)%Z ; 13%Z ; 17%Z ; 12%Z ; 16%Z ; (-18)%Z ; 13%Z ; 14%Z ; 17%Z ; (-8)%Z ; (-9)%Z] (cM (-17)%Z [:: (-12)%Z ; (-14)%Z ; (-7)%Z ; (-1)%Z ; 14%Z ; (-14)%Z ; (-13)%Z ; (-4)%Z ; 18%Z ; 13%Z ; (-9)%Z ; 15%Z ; (-10)%Z ; 18%Z ; 14%Z] [:: 8%Z ; (-14)%Z ; 9%Z ; 16%Z ; (-3)%Z ; (-8)%Z ; 9%Z ; (-9)%Z ; (-13)%Z ; 4%Z ; 15%Z ; 15%Z ; 6%Z ; (-14)%Z ; (-6)%Z] (cM 9%Z [:: 4%Z ; (-6)%Z ; 5%Z ; (-3)%Z ; (-6)%Z ; 18%Z ; 2%Z ; 10%Z ; 9%Z ; 17%Z ; (-12)%Z ; (-9)%Z ; 1%Z ; (-2)%Z] [:: (-10)%Z ; (-2)%Z ; 17%Z ; 14%Z ; 1%Z ; (-16)%Z ; 17%Z ; 18%Z ; (-3)%Z ; 4%Z ; (-14)%Z ; 17%Z ; 10%Z ; 7%Z] (cM 16%Z [:: (-15)%Z ; (-15)%Z ; (-18)%Z ; (-12)%Z ; 15%Z ; 7%Z ; (-11)%Z ; (-7)%Z ; (-8)%Z ; (-3)%Z ; (-17)%Z ; (-17)%Z ; (-12)%Z] [:: (-8)%Z ; 4%Z ; 12%Z ; (-7)%Z ; (-11)%Z ; 13%Z ; (-16)%Z ; 7%Z ; 16%Z ; (-1)%Z ; 16%Z ; 3%Z ; (-9)%Z] (cM (-15)%Z [:: 0%Z ; (-12)%Z ; 0%Z ; 16%Z ; 13%Z ; (-5)%Z ; 4%Z ; 1%Z ; 13%Z ; 11%Z ; 0%Z ; 16%Z] [:: 0%Z ; (-17)%Z ; (-10)%Z ; (-6)%Z ; 7%Z ; (-1)%Z ; 17%Z ; 8%Z ; 8%Z ; (-15)%Z ; (-16)%Z ; (-18)%Z] (cM 5%Z [:: 8%Z ; (-17)%Z ; (-15)%Z ; 0%Z ; 8%Z ; 1%Z ; (-2)%Z ; 14%Z ; 14%Z ; (-1)%Z ; (-7)%Z] [:: 14%Z ; (-11)%Z ; (-4)%Z ; (-18)%Z ; (-10)%Z ; (-11)%Z ; (-10)%Z ; (-6)%Z ; (-14)%Z ; (-13)%Z ; 5%Z] (cM (-7)%Z [:: 1%Z ; (-3)%Z ; (-7)%Z ; (-1)%Z ; 2%Z ; 14%Z ; 13%Z ; 7%Z ; 17%Z ; 7%Z] [:: 0%Z ; 1%Z ; (-7)%Z ; 12%Z ; (-1)%Z ; (-5)%Z ; (-12)%Z ; (-7)%Z ; 8%Z ; (-4)%Z] (cM 15%Z [:: (-18)%Z ; (-17)%Z ; 6%Z ; 1%Z ; (-13)%Z ; (-12)%Z ; 4%Z ; 13%Z ; 11%Z] [:: 12%Z ; 2%Z ; (-7)%Z ; (-18)%Z ; 0%Z ; 13%Z ; (-15)%Z ; (-16)%Z ; (-2)%Z] (cM 5%Z [:: (-9)%Z ; (-11)%Z ; 14%Z ; (-6)%Z ; (-11)%Z ; (-15)%Z ; (-12)%Z ; (-4)%Z] [:: (-12)%Z ; 8%Z ; (-8)%Z ; (-14)%Z ; 9%Z ; 3%Z ; 14%Z ; 3%Z] (cM (-18)%Z [:: 16%Z ; (-1)%Z ; 3%Z ; 11%Z ; 9%Z ; (-9)%Z ; 14%Z] [:: (-2)%Z ; (-7)%Z ; (-1)%Z ; 6%Z ; (-16)%Z ; 1%Z ; 6%Z] (cM 3%Z [:: (-8)%Z ; (-1)%Z ; (-1)%Z ; 15%Z ; 10%Z ; 6%Z] [:: 3%Z ; 7%Z ; 15%Z ; 12%Z ; 8%Z ; 5%Z] (cM (-14)%Z [:: (-2)%Z ; (-5)%Z ; 8%Z ; (-9)%Z ; 10%Z] [:: 12%Z ; 0%Z ; (-3)%Z ; 11%Z ; (-2)%Z] (cM 6%Z [:: (-8)%Z ; (-4)%Z ; (-9)%Z ; (-1)%Z] [:: 2%Z ; 5%Z ; (-8)%Z ; 0%Z] (cM (-14)%Z [:: (-8)%Z ; (-2)%Z ; 16%Z] [:: 11%Z ; 2%Z ; (-2)%Z] (cM 16%Z [:: (-14)%Z ; 9%Z] [:: (-17)%Z ; 8%Z] (cM (-18)%Z [:: (-11)%Z] [:: (-14)%Z] ((@eM _ _)))))))))))))))))))). *)

(* Time Eval vm_compute in ex_bdet 20 M20. *)

(*      = 75728050107481969127694371861%Z *)
(*      : CZmodule.Pack (Phant Z_comRingType) (CRing.class Z_cringType) *)
(*          Z_cringType *)
(* Finished transaction in 63. secs (62.825904u,0.016666s) *)
(* *) *)

(* End test. *)

(* (* Extraction Language Haskell. *) *)
(* (*  Extraction "Bareiss" ex_bdet. *) *)
