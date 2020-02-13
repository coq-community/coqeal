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

Section smith.

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

Variable E : euclidDomainType.


Variable find1 : forall m n, 'M[E]_(m.+1,n.+1) -> E -> option 'I_m.
Variable find2 : forall m n, 'M[E]_(m.+1,n.+1) -> E -> option ('I_(1+m) * 'I_n).
Variable find_pivot :
  forall m n, 'M[E]_(1 + m,1 + n) -> option ('I_(1 + m) * 'I_(1 + n)).

Hypothesis find1P : forall m n (E : 'M[E]_(1 + m,1 + n)) a,
  pick_spec [pred i | ~~(a %| E (lift 0 i) 0)] (find1 E a).
Hypothesis find2P : forall m n (E : 'M[E]_(1 + m,1 + n)) a,
  pick_spec [pred ij | ~~(a %| E ij.1 (lift 0 ij.2))] (find2 E a).
Hypothesis find_pivotP : forall m n (E : 'M[E]_(1 + m,1 + n)),
  pick_spec [pred ij | E ij.1 ij.2 != 0] (find_pivot E).

Fixpoint improve_pivot_rec k {m n} :
  'M[E]_(1 + m) -> 'M[E]_(1 + m, 1 + n) -> 'M[E]_(1 + n) ->
  'M[E]_(1 + m) * 'M[E]_(1 + m, 1 + n) * 'M[E]_(1 + n) :=
  match k with
  | 0 => fun P M Q => (P,M,Q)
  | p.+1 => fun P M Q =>
      let a := M 0 0 in
      if find1 M a is Some i then
        let Mi0 := M (lift 0 i) 0 in
        let P := Bezout_step a Mi0 P i in
        let M := Bezout_step a Mi0 M i in
        improve_pivot_rec p P M Q
      else
      let u  := dlsubmx M in let vM := ursubmx M in let vP := usubmx P in
      let u' := map_mx (fun x => 1 - odflt 0 (x %/? a)) u in
      let P  := col_mx (usubmx P) (u' *m vP + dsubmx P) in
      let M  := block_mx (a%:M) vM
                         (const_mx a) (u' *m vM + drsubmx M) in
      if find2 M a is Some (i,j) then
        let M := xrow 0 i M in let P := xrow 0 i P in
        let a := fun_of_matrix M 0 0 in
        let M0ij := fun_of_matrix M 0 (lift 0 j) in
        let Q := (Bezout_step a M0ij Q^T j)^T in
        let M := (Bezout_step a M0ij M^T j)^T in
        improve_pivot_rec p P M Q
      else (P, M, Q)
  end.

Definition improve_pivot k m n (M : 'M[E]_(1 + m, 1 + n)) :=
  improve_pivot_rec k 1 M 1.

(* TODO: Why is this so slow?? *)
Fixpoint Smith m n : 'M[E]_(m,n) -> 'M[E]_(m) * seq E * 'M[E]_(n) :=
  match m, n with
  | _.+1, _.+1 => fun M : 'M[E]_(1 + _, 1 + _) =>
      if find_pivot M is Some (i, j) then
      let a := fun_of_matrix M i j in let M := xrow i 0 (xcol j 0 M) in
      (* this is where Euclidean norm eases termination argument *)
      let: (P,M,Q) := improve_pivot (enorm a) M in
      let a  := fun_of_matrix M 0 0 in
      let u  := dlsubmx M in let v := ursubmx M in
      let v' := map_mx (fun x => odflt 0 (x %/? a)) v in
      let M  := ((drsubmx M) - (const_mx 1 *m v)) in
      let: (P', d, Q') := Smith (map_mx (fun x => odflt 0 (x %/? a)) M) in
      ((lift0_mx P' *m block_mx 1%:M 0 (- const_mx 1) 1%:M *m (xcol i 0 P)),
       a :: [seq x * a | x <- d],
       (xrow j 0 Q *m block_mx 1 (- v') 0 1%:M *m lift0_mx Q'))
    else (1, [::], 1)
  | _, _ => fun M => (1%:M, [::], 1%:M)
  end.

CoInductive improve_pivot_rec_spec m n P M Q :
  'M_(1 + m) * 'M_(1 + m,1 + n) * 'M[E]_(1 + n) -> Type :=
  ImprovePivotQecSpec P' M' Q' of P^-1 *m M *m Q^-1 = P'^-1 *m M' *m Q'^-1
  & (forall i j, M' 0 0 %| M' i j)
  & (forall i, M' i 0 = M' 0 0)
  & M' 0 0 %| M 0 0
  & P' \in unitmx & Q' \in unitmx
  : improve_pivot_rec_spec P M Q (P',M',Q').

Lemma unitrmxE k (M : 'M[E]_k.+1) : (M \is a GRing.unit) = (M \in unitmx).
Proof. by []. Qed.

Definition unitmxEE := (unitmx_mul, unitmx_tr, unit_Bezout_mx, unitmx_perm).

Lemma improve_pivot_recP :
  forall k m n (P : 'M_(1 + m)) (M : 'M_(1 + m,1 + n)) Q,
  (enorm (M 0%R 0%R) <= k)%N -> M 0 0 != 0 ->
   P \in unitmx -> Q \in unitmx ->
    improve_pivot_rec_spec P M Q (improve_pivot_rec k P M Q).
Proof.
elim=> [m n L M R0|k IHk m n L M R0 Hk nzM00 unitL unitR /=].
  by rewrite leqn0 => /eqP /enorm_eq0 ->; rewrite eqxx.
case: find1P=> [i Hi|Hi].
  have [||||L' A' R' HA' ? ? Hdiv HL' HR'] // := IHk; do ?constructor => //.
  + by rewrite -ltnS (leq_trans (ltn_enorm nzM00 (sdvd_Bezout_step Hi)) Hk).
  + by rewrite -eqdr0 (congr_eqd (Bezout_step_mx00 M) (eqdd _)) eqdr0 gcdr_eq0
               (negbTE nzM00).
  + by rewrite Bezout_stepE !unitmxEE.
  + rewrite -HA' !Bezout_stepE invrM ?unit_Bezout_mx // !mulmxA.
    by congr (_ *m _ *m _); rewrite -mulmxA mulVmx ?unit_Bezout_mx // mulmx1.
  + rewrite (eqd_dvd (eqdd _) (Bezout_step_mx00 _)) in Hdiv.
    exact: (dvdr_trans Hdiv (dvdr_gcdl _ _)).
set P := map_mx _ _.
have Hblock : (matrix.block_mx 1 0 P 1%:M) *m M =
               matrix.block_mx (M 0 0)%:M (matrix.ursubmx M)
              (matrix.const_mx (M 0 0)) (P *m matrix.ursubmx M + matrix.drsubmx M).
  rewrite -{1}[M]submxK mulmx_block !mul0mx !mul1mx !addr0
          [matrix.ulsubmx M]mx11_scalar 2!mxE !lshift0.
  congr matrix.block_mx; rewrite mul_mx_scalar.
  apply/matrixP=> p q; rewrite ord1 !mxE lshift0 mulrBr mulr1 !rshift1.
  case: odivrP=> [d ->|]; first by rewrite mulrC subrK.
  by case/dvdrP:(negbFE (Hi p))=> x -> /(_ x); rewrite eqxx.
have unit_block : matrix.block_mx 1 0 P 1%:M \in unitmx
  by rewrite unitmxE (det_lblock 1 P) !det1 mul1r unitr1.
have HblockL : (matrix.block_mx 1 0 P 1%:M) *m L =
  matrix.col_mx (matrix.usubmx L) (P *m matrix.usubmx L + matrix.dsubmx L)
  by rewrite -{1}[L]vsubmxK mul_block_col !mul1mx mul0mx addr0.
case: find2P=> [[i j]|Hij] /=.
  set B := matrix.block_mx _ _ _ _; set A := matrix.xrow _ _ B => Hij.
  have HMA: M 0 0 = A^T 0 0.
    rewrite /A /B -{4}(lshift0 n 0) !mxE tpermL.
    by case: splitP=> [i' _|i' Hi']; rewrite ?ord1 row_mxEl mxE ?eqxx.
  rewrite HMA in nzM00 Hk Hij; rewrite -[A]trmxK [A^T^T^T]trmxK ![A^T^T _ _]mxE.
  case: IHk => [||||L' A' R' HA' ? ? Hdiv HL' HR']; do ?constructor=> //.
  + rewrite -ltnS mxE (leq_trans _ Hk) ?(ltn_enorm nzM00) ?sdvd_Bezout_step //.
    by rewrite {2}/A [_ (lift _ _) _]mxE [matrix.xrow _ _ _ _ _]mxE tpermL.
  + by rewrite mxE -eqdr0 (congr_eqd (Bezout_step_mx00 _) (eqdd _)) eqdr0
               gcdr_eq0 (negbTE nzM00).
  + by rewrite xrowE -HblockL !unitmxEE unit_block.
  + by rewrite !Bezout_stepE !unitmxEE.
  + rewrite -HA' ![(A^T) 0 _]mxE /A /B -Hblock -HblockL !xrowE.
    rewrite !Bezout_stepE !trmx_mul !trmxK !invrM //.
    - rewrite !mulmxA -[_ / _ *m _]mulmxA mulVmx ?unitmx_perm // mulmx1.
      rewrite -[_ / _ *m _]mulmxA mulVmx // mulmx1 -[_ *m _^T *m _]mulmxA.
      by rewrite mulmxV ?unitmx_tr ?unit_Bezout_mx // mulmx1.
    - by rewrite unitmx_tr unit_Bezout_mx.
    - by rewrite unitmx_perm.
    by rewrite !unitmxEE unit_block.
  rewrite (dvdr_trans Hdiv) // mxE (eqd_dvd (Bezout_step_mx00 _) (eqdd _)) HMA.
  exact: dvdr_gcdl.
constructor=> //; first by rewrite -HblockL -Hblock invrM // mulmxA mulmxKV.
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
by rewrite -HblockL unitmx_mul unitmxE (det_lblock 1 P) !det1 mulr1 unitr1.
Qed.

CoInductive improve_pivot_spec m n M :
  'M[E]_(1 + m) * 'M_(1 + m,1 + n) * 'M_(1 + n) -> Type :=
  ImprovePivotSpec L A R of L *m M *m R = A
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & L \in unitmx & R \in unitmx
  : improve_pivot_spec M (L,A,R).

Lemma improve_pivotP k m n (M : 'M_(1 + m, 1 + n)) :
  (enorm (M 0%R 0%R) <= k)%N -> M 0 0 != 0 ->
  improve_pivot_spec M (improve_pivot  k M).
Proof.
move=> ? ?; rewrite /improve_pivot.
have := (@improve_pivot_recP k _ _ 1%:M M 1%:M).
rewrite /improve_pivot_rec=> [[]] //; rewrite ?unitmx1 //.
rewrite !invr1 mul1mx mulmx1 => ? ? ? eqM ? ? ? ? ?.
by constructor=> //; rewrite eqM !mulmxA mulmxV // mul1mx mulmxKV.
Qed.

Lemma SmithP : forall (m n : nat) (M : 'M_(m,n)),
  smith_spec M (Smith  M).
Proof.
elim=> [n M|m IHn]; first constructor; rewrite ?unitmx1 //.
  rewrite [M]flatmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case: (i == j :> nat).
case=> [M|n M /=]; first constructor; rewrite ?sorted_nil ?mxE ?unitmx1 //.
  rewrite [M]thinmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case: (i == j :> nat).
case: find_pivotP =>[[i j] HMij | H].
  case: improve_pivotP; rewrite ?mxE ?tpermR ?leqnn //.
  rewrite -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N => L A R0 HA Hdiv HAi0 HA00.
  set A' := map_mx _ _; set v' := map_mx _ _.
  case: IHn=> L' d R' Hd Hsorted HL' HR' HL HR; constructor.
  * rewrite xcolE xrowE -!mulmxA (mulmxA M) -xcolE (mulmxA (tperm_mx _ _)).
    rewrite -xrowE (mulmxA L) (mulmxA _ R0) HA mulmx_block !mulmxA mulmx_block.
    rewrite -{1}(submxK A) !mulmx_block.
    do 2! rewrite !mul0mx !mulmx0 !mulmx1 !mul1mx !addr0 ?add0r.
    have Hu: matrix.const_mx 1 *m matrix.ulsubmx A = matrix.dlsubmx A.
      rewrite [matrix.ulsubmx A]mx11_scalar mul_mx_scalar; apply/matrixP=> k l.
      by rewrite ord1 !mxE mulr1 !lshift0 !HAi0.
    have Hv': (matrix.ulsubmx A *m v') = matrix.ursubmx A.
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
      transitivity (A 0 0 *: (L' *m A' *m R')).
      rewrite -[_ *m A' *m _]mulmxA scalemxAr scalemxAl.
      have Hdiv' : forall i j, A 0 0 %| (matrix.drsubmx A - matrix.const_mx 1 *m matrix.ursubmx A) i j.
        by move=> k l; rewrite !mxE big_ord1 !mxE mul1r dvdr_sub ?Hdiv.
      have -> : A 0 0 *: A' = matrix.drsubmx A - matrix.const_mx 1 *m matrix.ursubmx A.
        apply/matrixP=> k l; rewrite 2!mxE.
        case: odivrP=>[x ->|H]; first by rewrite mulrC.
        by case/dvdrP:(Hdiv' k l)=> q /eqP; rewrite (negbTE (H q)).
      by rewrite mulmxA.
    rewrite Hd; apply/matrixP=> k l; rewrite !mxE.
    case: (k == l :> nat); last by rewrite mulr0.
    have [Hk|Hk] := (ltnP k (size d)).
      by rewrite (nth_map 0 _ _ Hk) mulrC.
    by rewrite !nth_default ?size_map ?Hk // mulr0.
  * have {HA00}HA00: A 0 0 != 0.
      by apply/eqP=> H; move:HA00; rewrite H dvd0r (negbTE HMij).
    rewrite /= path_min_sorted;
      last by apply/allP=> a /mapP [b _ ->]; exact:dvdr_mull.
    case: d Hsorted {Hd} => //= a d; elim: d a=> //= a1 d IHd a0 /andP[a01 /IHd].
    by rewrite dvdr_mul2r ?a01.
  * rewrite xcolE !unitmx_mul unitmx_perm HL !unitmxE.
    by rewrite !det_lblock !det1 mul1r mulr1 unitr1 -unitmxE !andbT.
  * rewrite xrowE !unitmx_mul unitmx_perm HR !unitmxE.
   by rewrite 2!det_ublock 2!det1 2!mul1r unitr1 -unitmxE.
constructor =>[|||]; rewrite ?mxE ?unitmx1 //.
rewrite mul1mx mulmx1; apply/matrixP=> i j; rewrite !mxE (eqP (negbFE (H (i,j)))).
by case: (i == j :> nat); rewrite ?nth_nseq ?if_same nth_nil.
Qed. (* Why is this so slow??? *)

Lemma size_Smith m n (A : 'M_(m,n)) :
  let: (_, d, _) := (Smith  A) in (size d <= minn m n)%N.
Proof.
elim: m n A=>[n'|m' Ih n']; first by rewrite min0n.
case: n'=>[|n' A /=]; first by rewrite minn0.
case: find_pivotP=> [[x1 x2] Hx|//].
case: (improve_pivot _ _); case => a b c /=; set M := map_mx _ _.
case H: (Smith _) (Ih n' M) => [[i s] k] /=.
by rewrite size_map minnSS ltnS.
Qed.

Definition euclidEDRMixin := EDR.Mixin SmithP.
Canonical euclidEDRType   := Eval hnf in EDRType E euclidEDRMixin.

End smith.
