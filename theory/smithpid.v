(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
(* Require Import ZArith. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
From mathcomp Require Import ssralg ssrint ssrnum fintype.
From mathcomp Require Import matrix mxalgebra bigop zmodp perm.
Require Import edr dvdring mxstructure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section smith_def.

(* Two-steps approach:

1) Make the first column look like
  ___
 / g \
 | g |
 | . |
 | . |
 | g |
 \___/

2)

For any i j s.t. ~~ g %| M i j, xrow 0 i M, bezout step on the first row
and back to 1) *)

Variable R : pidType.

Variable find1 : forall m n, 'M[R]_(m.+1,n.+1) -> R -> option 'I_m.
Variable find2 :
  forall m n, 'M[R]_(m.+1,n.+1) -> R -> option ('I_(1 + m) * 'I_n).

Hypothesis find1P : forall m n (M : 'M[R]_(1 + m,1 + n)) a,
  pick_spec [pred i | ~~(a %| M (lift 0 i) 0)] (find1 M a).
Hypothesis find2P : forall m n (M : 'M[R]_(1 + m,1 + n)) a,
  pick_spec [pred ij | ~~(a %| M ij.1 (lift 0 ij.2))] (find2 M a).

(* This lemma is used in the termination proof of improve_pivot_rec *)
Lemma sdvd_Bezout_step2 m n i j u' vM (M : 'M[R]_(1 + m, 1 + n)) :
  let B : 'M_(1 + m, 1 + n) := block_mx (M 0 0)%:M vM (const_mx (M 0 0)) (u' *m vM + drsubmx M) in
  let C := xrow 0 i B in
  ~~ (M 0 0 %| B i (lift 0 j)) ->
  (Bezout_step (C 0 0) (C 0 (lift 0 j)) C^T j)^T 0 0 %<| M 0 0.
Proof.
set B := block_mx _ _ _ _ => /=.
set C := xrow _ _ _.
have ->: M 0 0 = C^T 0 0.
  rewrite /C /B -(lshift0 n 0) !mxE tpermL.
  by case: splitP=> [i' _|i' Hi']; rewrite ?ord1 row_mxEl mxE ?eqxx.
move=> ndvd.
rewrite mxE.
rewrite -[C]trmxK [C^T^T^T]trmxK ![C^T^T _ _]mxE sdvd_Bezout_step //.
by rewrite {2}/C [_ (lift _ _) _]mxE [matrix.xrow _ _ _ _ _]mxE tpermL.
Qed.

Fixpoint improve_pivot_rec {m n} (P : 'M[R]_(1 + m)) (M : 'M[R]_(1 + m, 1 + n))
         (Q : 'M[R]_(1 + n)) (k : Acc (@sdvdr R) (M 0 0)) :
         'M[R]_(1 + m) * 'M[R]_(1 + m, 1 + n) * 'M[R]_(1 + n) :=
    match k with Acc_intro IHa =>
      if find1P M (M 0 0) is Pick i Hi then
        let Ai0 := M (lift 0 i) 0 in
        let P := Bezout_step (M 0 0) Ai0 P i in
        improve_pivot_rec P Q (IHa _ (sdvd_Bezout_step Hi))
      else
        let u  := dlsubmx M in
        let vM := ursubmx M in
        let vP := usubmx P in
        let u' := map_mx (fun x => 1 - odflt 0 (x %/? M 0 0)) u in
        let P  := col_mx (usubmx P) (u' *m vP + dsubmx P) in
        let A  := block_mx (M 0 0)%:M vM
                           (const_mx (M 0 0)) (u' *m vM + drsubmx M) in
        if find2P A (M 0 0) is Pick (i,j) Hij then
          let A := xrow 0 i A in
          let P := xrow 0 i P in
          let a := A 0 0 in
          let A0j := A 0 (lift 0 j) in
          let Q := (Bezout_step a A0j Q^T j)^T in
          improve_pivot_rec P Q (IHa _ (sdvd_Bezout_step2 Hij))
        else (P, A, Q)
    end.

Variable find_pivot :
  forall m n, 'M[R]_(1 + m,1 + n) -> option ('I_(1 + m) * 'I_(1 + n)).

Definition improve_pivot m n (M : 'M[R]_(1 + m, 1 + n)) :=
  improve_pivot_rec 1 1 (sdvdr_wf (M 0 0)).

Fixpoint Smith {m n} : 'M[R]_(m,n) -> 'M[R]_(m) * seq R * 'M[R]_(n) :=
  match m, n return 'M[R]_(m, n) -> 'M[R]_(m) * seq R * 'M[R]_(n) with
  | _.+1, _.+1 => fun M : 'M[R]_(1 + _, 1 + _) =>
      if find_pivot M is Some (i, j) then
      let a := fun_of_matrix M i j in let A := xrow i 0 (xcol j 0 M) in
      let: (P,A,Q) := improve_pivot A in
      let a  := fun_of_matrix A 0 0 in
      let u  := dlsubmx A in let v := ursubmx A in
      let v' := map_mx (fun x => odflt 0 (x %/? a)) v in
      let A  := ((drsubmx A) - (const_mx 1 *m v)) in
      let: (P', d, Q') := Smith (map_mx (fun x => odflt 0 (x %/? a)) A) in
      ((lift0_mx P' *m block_mx 1%:M 0 (- const_mx 1) 1%:M *m (xcol i 0 P)),
       a :: [seq x * a | x <- d],
       (xrow j 0 Q *m block_mx 1 (- v') 0 1%:M *m lift0_mx Q'))
    else (1, [::], 1)
  | _, _ => fun M => (1%:M, [::], 1%:M)
  end.

Hypothesis find_pivotP : forall m n (M : 'M[R]_(1 + m,1 + n)),
  pick_spec [pred ij | M ij.1 ij.2 != 0] (find_pivot M).

Variant improve_pivot_rec_spec m n P M Q :
  'M[R]_(1 + m) * 'M[R]_(1 + m,1 + n) * 'M[R]_(1 + n) -> Type :=
  ImprovePivotRecSpec P' A Q' of P^-1 *m M *m Q^-1 = P'^-1 *m A *m Q'^-1
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & P' \in unitmx & Q' \in unitmx
  : improve_pivot_rec_spec P M Q (P',A,Q').

Lemma unitrmxE k (M : 'M[R]_k.+1) : (M \is a GRing.unit) = (M \in unitmx).
Proof. by []. Qed.

Definition unitmxEE := (unitmx_mul, unitmx_tr, unit_Bezout_mx, unitmx_perm).

Scheme Acc_rect_dep := Induction for Acc Sort Type.

Lemma improve_pivot_recP :
  forall m n (P : 'M_(1 + m)) (M : 'M_(1 + m,1 + n)) Q (k : Acc (@sdvdr R) (M 0 0)),
   M 0 0 != 0 ->
   P \in unitmx -> Q \in unitmx ->
    improve_pivot_rec_spec P M Q (improve_pivot_rec P Q k).
Proof.
move=> m n P M Q k.
rewrite -/(ecast a (Acc (fun x y : R => x %<| y) a) (erefl (M 0 0)) k).
move: (erefl _) => eq_M00; move: eq_M00 k.
move: {1 3 5}(fun_of_matrix M 0 0) => a eq_a k.
elim/Acc_rect_dep: k M P Q eq_a => a' Acc_a' IHa' M P Q eq_a' nzM00 unitL unitR /=.
move: (eq_a') Acc_a' IHa'.
rewrite eq_a' => {}eq_a' Acc_a' IHa'; rewrite {eq_a'}[eq_a']eq_axiomK /=.
case: find1P=> [i Hi|Hi].
set P0 := Bezout_step _ _ P _; set M0 := Bezout_step _ _ M _.
have /(_ erefl) [|||P' A' Q' HA' ? ? Hdiv HP' HQ'] // :=
  IHa' (M0 0 0) (sdvd_Bezout_step Hi) M0 P0 Q.
  + by rewrite -eqdr0 (congr_eqd (Bezout_step_mx00 M) (eqdd _)) eqdr0 gcdr_eq0
               (negbTE nzM00).
  + by rewrite /P0 Bezout_stepE !unitmxEE.
  + constructor=> //.
      rewrite -HA' /P0 /M0 !Bezout_stepE invrM ?unit_Bezout_mx // !mulmxA.
      by congr (_ *m _ *m _); rewrite -mulmxA mulVmx ?unit_Bezout_mx // mulmx1.
  + rewrite (eqd_dvd (eqdd _) (Bezout_step_mx00 _)) in Hdiv.
    exact: (dvdr_trans Hdiv (dvdr_gcdl _ _)).
set M' := map_mx _ _.
have Hblock : (matrix.block_mx 1 0 M' 1%:M) *m M =
               matrix.block_mx (M 0 0)%:M (matrix.ursubmx M)
              (matrix.const_mx (M 0 0)) (M' *m matrix.ursubmx M + matrix.drsubmx M).
  rewrite -{1}[M]submxK mulmx_block !mul0mx !mul1mx !addr0
          [matrix.ulsubmx M]mx11_scalar 2!mxE !lshift0.
  congr matrix.block_mx; rewrite mul_mx_scalar.
  apply/matrixP=> p q; rewrite ord1 !mxE lshift0 mulrBr mulr1 !rshift1.
  case: odivrP=> [d ->|]; first by rewrite mulrC subrK.
  by case/dvdrP:(negbFE (Hi p))=> x -> /(_ x); rewrite eqxx.
have unit_block : matrix.block_mx 1 0 M' 1%:M \in unitmx
  by rewrite unitmxE (det_lblock 1 M') !det1 mul1r unitr1.
have HblockP : (matrix.block_mx 1 0 M' 1%:M) *m P =
  matrix.col_mx (matrix.usubmx P) (M' *m matrix.usubmx P + matrix.dsubmx P)
  by rewrite -{1}[P]vsubmxK mul_block_col !mul1mx mul0mx addr0.
case: find2P=> [[i j]|Hij] /=.
  set B := matrix.block_mx _ _ _ _; set C := matrix.xrow _ _ B => Hij.
  have HMA: M 0 0 = C^T 0 0.
    rewrite /C /B -{4}(lshift0 n 0) !mxE tpermL.
    by case: splitP=> [i' _|i' Hi']; rewrite ?ord1 row_mxEl mxE ?eqxx.
  rewrite HMA in nzM00.
set P0 := xrow _ _ _; set Q0 := (Bezout_step _ _ Q^T _)^T.
set M0 := (Bezout_step _ _ C^T _)^T; set dvd_prf := sdvd_Bezout_step2 _.
have /(_ erefl) [|||P' A' Q' HA' ? ? Hdiv HP' HQ'] // :=
  IHa' (M0 0 0) dvd_prf M0 P0 Q0.
  + rewrite /M0 -[C]trmxK [C^T^T^T]trmxK ![C^T^T _ _]mxE.
    by rewrite mxE -eqdr0 (congr_eqd (Bezout_step_mx00 _) (eqdd _)) eqdr0
               gcdr_eq0 (negbTE nzM00).
  + by rewrite /P0 xrowE -HblockP !unitmxEE unit_block.
  + by rewrite /Q0 !Bezout_stepE !unitmxEE.
  + constructor=> //.
  + rewrite -HA' /P0 /M0 /Q0 -[C]trmxK [C^T^T^T]trmxK ![C^T^T _ _]mxE.
    rewrite ![(C^T) 0 _]mxE /C /B -Hblock -HblockP !xrowE.
    rewrite !Bezout_stepE !trmx_mul !trmxK !invrM //.
    - rewrite !mulmxA -[_ / _ *m _]mulmxA mulVmx ?unitmx_perm // mulmx1.
      rewrite -[_ / _ *m _]mulmxA mulVmx // mulmx1 -[_ *m _^T *m _]mulmxA.
      by rewrite mulmxV ?unitmx_tr ?unit_Bezout_mx // mulmx1.
    - by rewrite unitmx_tr unit_Bezout_mx.
    - by rewrite unitmx_perm.
    by rewrite !unitmxEE unit_block.
  rewrite /M0 -[C]trmxK [C^T^T^T]trmxK ![C^T^T _ _]mxE in Hdiv.
  rewrite (dvdr_trans Hdiv) // mxE (eqd_dvd (Bezout_step_mx00 _) (eqdd _)) HMA.
  exact: dvdr_gcdl.
constructor=> //; first by rewrite -HblockP -Hblock invrM // mulmxA mulmxKV.
+ rewrite -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N => i j.
  rewrite -{3}(lshift0 m 0) -{3}(lshift0 n 0) block_mxEul mxE eqxx !mxE.
(* Why do we have to specify all these arguments? *)
  case: splitP=> i' Hi'; rewrite mxE; case: splitP=> j' Hj'; rewrite ?mxE ?ord1 //.
    by move: (negbFE (Hij (lshift m 0,j'))); rewrite -rshift1 block_mxEur !mxE.
  by move: (negbFE (Hij (lift 0 i',j'))); rewrite -!rshift1 block_mxEdr !mxE.
+ rewrite -[m.+1]/(1 + m)%N => i.
  rewrite -{5}(lshift0 m 0) -{3 6}(lshift0 n 0) (block_mxEul (M 0 0)%:M _) !mxE.
  by case: splitP=> i' _; rewrite row_mxEl !mxE ?ord1.
+ rewrite -{3}(lshift0 m 0) -{3}(lshift0 n 0).
  by rewrite (block_mxEul (M 0 0)%:M (matrix.ursubmx M)) mxE dvdrr.
by rewrite -HblockP unitmx_mul unitmxE (det_lblock 1 M') !det1 mulr1 unitr1.
Qed.

Variant improve_pivot_spec m n M :
  'M[R]_(1 + m) * 'M[R]_(1 + m,1 + n) * 'M[R]_(1 + n) -> Type :=
  ImprovePivotSpec P A Q of P *m M *m Q = A
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & P \in unitmx & Q \in unitmx
  : improve_pivot_spec M (P,A,Q).

Lemma improve_pivotP m n (M : 'M_(1 + m, 1 + n)) :
  M 0 0 != 0 -> improve_pivot_spec M (improve_pivot M).
Proof.
move=> ?; rewrite /improve_pivot.
have := (@improve_pivot_recP _ _ 1%:M M 1%:M (sdvdr_wf _)).
case; rewrite ?unitmx1 // !invr1 mul1mx mulmx1 => ? ? ? eqM ? ? ? ? ?.
by constructor=> //; rewrite eqM !mulmxA mulmxV // mul1mx mulmxKV.
Qed.

Lemma SmithP : forall (m n : nat) (M : 'M_(m,n)),
  smith_spec M (Smith M).
Proof.
elim=> [n M|m IHn]; first constructor; rewrite ?unitmx1 //.
  rewrite [M]flatmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case: (i == j :> nat).
case=> [M|n M /=]; first constructor; rewrite ?sorted_nil ?mxE ?unitmx1 //.
  rewrite [M]thinmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case: (i == j :> nat).
case: find_pivotP =>[[i j] HMij | H].
  case: improve_pivotP; rewrite ?mxE ?tpermR ?leqnn //.
  rewrite -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N => L B Q0 HB Hdiv HAi0 HA00.
  set A' := map_mx _ _; set v' := map_mx _ _.
  case: IHn=> L' d Q' Hd Hsorted HL' HQ' HL HQ; constructor.
  * rewrite xcolE xrowE -!mulmxA (mulmxA M) -xcolE (mulmxA (tperm_mx _ _)).
    rewrite -xrowE (mulmxA L) (mulmxA _ Q0) HB mulmx_block !mulmxA mulmx_block.
    rewrite -{1}(submxK B) !mulmx_block.
    do 2! rewrite !mul0mx !mulmx0 !mulmx1 !mul1mx !addr0 ?add0r.
    have Hu: matrix.const_mx 1 *m matrix.ulsubmx B = matrix.dlsubmx B.
      rewrite [matrix.ulsubmx B]mx11_scalar mul_mx_scalar; apply/matrixP=> k l.
      by rewrite ord1 !mxE mulr1 !lshift0 !HAi0.
    have Hv': (matrix.ulsubmx B *m v') = matrix.ursubmx B.
      apply/matrixP=> k l.
      rewrite (ord1 k) !mxE big_ord_recl big_ord0 !mxE !lshift0 addr0.
      case: odivrP=>[x ->|H]; first by rewrite mulrC.
      by case/dvdrP:(Hdiv 0 (rshift 1 l))=> q /eqP; rewrite (negbTE (H q)).
    rewrite diag_mx_seq_cons; congr matrix.block_mx.
    (* Pivot *)
    + by apply/matrixP=> k l; rewrite !ord1 !mxE !lshift0 eqxx.
    (* Horizontal zeros *)
    + by rewrite mulNmx mulmxN mulmxA Hv' addNr.
    (* Vertical zeros *)
    + by rewrite mulmxN mulNmx -mulmxA Hu addNr.
    (* down-right submatrix *)
    + rewrite mulmxN !mulNmx -mulmxA Hu addNr mul0mx add0r addrC -mulmxA -mulmxBr.
      transitivity (B 0 0 *: (L' *m A' *m Q')).
      rewrite -[_ *m A' *m _]mulmxA scalemxAr scalemxAl.
      have Hdiv' : forall i j, B 0 0 %| (matrix.drsubmx B - matrix.const_mx 1 *m matrix.ursubmx B) i j.
        by move=> k l; rewrite !mxE big_ord1 !mxE mul1r dvdr_sub ?Hdiv.
      have -> : B 0 0 *: A' = matrix.drsubmx B - matrix.const_mx 1 *m matrix.ursubmx B.
        apply/matrixP=> k l; rewrite 2!mxE.
        case: odivrP=>[x ->|H]; first by rewrite mulrC.
        by case/dvdrP:(Hdiv' k l)=> q /eqP; rewrite (negbTE (H q)).
      by rewrite mulmxA.
    rewrite Hd; apply/matrixP=> k l; rewrite !mxE.
    case: (k == l :> nat); last by rewrite mulr0.
    have [Hk|Hk] := (ltnP k (size d)).
      by rewrite (nth_map 0 _ _ Hk) mulrC.
    by rewrite !nth_default ?size_map ?Hk // mulr0.
  * have {}HA00: B 0 0 != 0.
      by apply/eqP=> H; move:HA00; rewrite H dvd0r (negbTE HMij).
    rewrite /= path_min_sorted;
      last by apply/allP => a /mapP [b _ ->]; exact:dvdr_mull.
    case: d Hsorted {Hd} => //= a d; elim: d a=> //= a1 d IHd a0 /andP[a01 /IHd].
    by rewrite dvdr_mul2r ?a01.
  * rewrite xcolE !unitmx_mul unitmx_perm HL !unitmxE.
    by rewrite !det_lblock !det1 mul1r mulr1 unitr1 -unitmxE !andbT.
  * rewrite xrowE !unitmx_mul unitmx_perm HQ !unitmxE.
   by rewrite 2!det_ublock 2!det1 2!mul1r unitr1 -unitmxE.
constructor =>[|||]; rewrite ?mxE ?unitmx1 //.
rewrite mul1mx mulmx1; apply/matrixP=> i j; rewrite !mxE (eqP (negbFE (H (i,j)))).
by case: (i == j :> nat); rewrite ?nth_nseq ?if_same nth_nil.
Qed. (* Why is this so slow??? *)

Lemma size_Smith m n (M : 'M_(m,n)) :
  let: (_, d, _) := Smith M in (size d <= minn m n)%N.
Proof.
elim: m n M => [n'|m' Ih n']; first by rewrite min0n.
case: n' => [|n' M /=]; first by rewrite minn0.
case: find_pivotP=> [[x1 x2] Hx|//].
case: (improve_pivot _); case => a b c /=.
case H: (Smith _)=>[[i j] k].
rewrite /= size_map minnSS ltnS.
move: (Ih n' (map_mx (fun x => odflt 0 (x %/? b 0 0))
             (drsubmx b - const_mx 1 *m ursubmx b))).
by rewrite H.
Qed.

Definition pidEDRMixin := EDR.Mixin SmithP.
Canonical pidEDRType   := Eval hnf in EDRType R pidEDRMixin.

End smith_def.
