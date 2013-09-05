Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg ssrint ssrnum fintype.
Require Import dvdring matrix mxalgebra bigop zmodp perm mxstructure.
Require Import refinements seqmatrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section Bezout_mx.

Variable R : bezoutRingType.

(*****************
  if the following Bezout identity holds: u * a1 + v * b1 = 1,
  Bezout_mx a b n k represents the following matrix (dots are zeros):
    
          (kth column)
  / u .... v ..... \
  | . 1 .......... |
  | ....1......... |
  | -b1 .. a1 .... | (kth row)
  | ..........1... |
  \ .............1 /


  (determinant is +/-1)
******************)

Definition combine_mx (a b c d : R) (m : nat) (k : 'I_m) :=
  let k' := rshift 1 k in
  let d := \row_j (a *+ (j == 0) + d *+ (j == k') + ((j != 0) && (j != k'))%:R) in
  diag_mx d + c *: delta_mx k' 0 + b *: delta_mx 0 k'.

Definition combine_step (a b c d : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :=
  let k' := rshift 1 k in
  let r0 := a *: row 0 M + b *: row k' M in
  let rk := c *: row 0 M + d *: row k' M in
  \matrix_i (r0 *+ (i == 0) + rk *+ (i == k') + row i M *+ ((i != 0) && (i != k'))).

Lemma combine_stepE (a b c d : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
  combine_step a b c d M k = combine_mx a b c d k *m M.
Proof.
rewrite /combine_step /combine_mx; apply/matrixP=> i j.
have [g u v a' b' _ _ _ _] := egcdrP a b.
rewrite !mxE (bigD1 (0 : 'I_m.+1)) // !mxE (bigD1 (rshift 1 k)) // !mxE /=.
case H:(i==0).
  rewrite big1=> [|l /andP [H1 H2]].
    rewrite (eqP H) !eqxx !mulr1n !mxE !mulr0 !addr0.
    by rewrite !mulr1 mulr0n add0r.
  rewrite !mxE (eqP H) (eq_sym 0 l) (negbTE H1) (negbTE H2).
  by rewrite mulr0n !mulr0 !add0r mul0r.
case H':(i==rshift 1 k).
  rewrite big1=> [|l /andP [H1 H2]].
    rewrite (eqP H') !eqxx !mulr1n !mxE !mulr0 !addr0.
    by rewrite !mulr1 mulr0n !add0r addrC.
  rewrite !mxE (eqP H') !(eq_sym (rshift 1 k) l) eqxx (negbTE H1) (negbTE H2).
  by rewrite mulr0n !mulr0 !add0r mul0r.
rewrite (bigD1 i); last by rewrite H H'.
rewrite !mxE big1=> [/=|l /andP [/andP [H1 H2] H3]].
  rewrite H H' eqxx !mulr0n !mulr0 !mulr1n.
  by rewrite !addr0 !mul0r !add0r mul1r.
rewrite !mxE H H' (negbTE H1) (negbTE H2) (eq_sym i l) (negbTE H3) /=.
by rewrite mulr0n !mulr0 !addr0 mul0r.
Qed.

Lemma combine_mx_inv (a b c d : R) m (k : 'I_m) :
  a * d - b * c = 1 ->
  combine_mx a b c d k *m combine_mx d (-b) (-c) a k = 1%:M.
Proof.
move=> H; rewrite -combine_stepE; apply/matrixP=> i j; rewrite !mxE.
case Hi:(i==0).
  rewrite !mxE (eqP Hi) !eqxx !mulr0 mxE !addr0 (eq_sym 0 j).
  case Hj:(j==0).
    rewrite (eqP Hj) mulr1 !mulr0.
    by rewrite addr0 sub0r mulrN.
  rewrite !mulr0 !add0r addr0 (eq_sym _ j).
  case:(j==rshift 1 k); last by rewrite !mulr0 add0r.
  by rewrite mulr1 mulr1n mulrN mulrC addNr.
case Hj:(j==0).
  rewrite !mxE (eqP Hj) Hi add0r.
  case Hk:(i==rshift 1 k).
    rewrite !mxE !eqxx !mulr0 mulr1 !addr0 !add0r.
    by rewrite mulrN addrC mulrC addNr.
  by rewrite !mxE Hi Hk eqxx !add0r !mulr0 addr0.
case Hk:(i==rshift 1 k).
  rewrite !mxE (eq_sym 0 j) Hj (eqP Hk) !eqxx !mulr0 !addr0 !add0r.
  rewrite (eq_sym _ j).
  case:(j==rshift 1 k); last by rewrite !mulr0 addr0.
  by rewrite !mulr1 addrC mulrN (mulrC c) (mulrC d).
by rewrite !mxE Hi Hj Hk !mulr0 !add0r !addr0.
Qed.

Definition Bezout_mx (a b : R) (m : nat) (k : 'I_m) :=
  let:(_,u,v,a1,b1) := egcdr a b in combine_mx u v (-b1) a1 k.

Definition Bezout_step (a b : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :=
  let:(_,u,v,a1,b1) := egcdr a b in combine_step u v (-b1) a1 M k.

Lemma Bezout_stepE a b (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
  Bezout_step a b M k = Bezout_mx a b k *m M.
Proof.
rewrite /Bezout_step /Bezout_mx; have [g u v a' b' _ _ _ _] := egcdrP.
by rewrite combine_stepE.
Qed.

Lemma Bezout_step_mx00 m n (M : 'M_(1 + m,1 + n)) {k : 'I_m} :
 (Bezout_step (M 0 0) (M (rshift 1 k) 0) M k) 0 0 %= gcdr (M 0 0) (M (rshift 1 k) 0).
rewrite /Bezout_step; have [g u v a' b' Bezout_a'b' gcd_g H1 H2] := egcdrP.
by rewrite !mxE !addr0 {1}H1 {1}H2 !mulrA -mulrDl Bezout_a'b' mul1r.
Qed.

Lemma sdvd_Bezout_step (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
 ~~ (M 0 0 %| M (rshift 1 k) 0) ->
 (Bezout_step (M 0 0) (M (rshift 1 k) 0) M k) 0 0 %<| M 0 0.
Proof.
move=> H; rewrite /sdvdr (eqd_dvd (Bezout_step_mx00 _) (eqdd _)) dvdr_gcdl.
rewrite (eqd_dvd (eqdd _ ) (Bezout_step_mx00 _)).
by apply/negP=> H'; rewrite (dvdr_trans H' (dvdr_gcdr _ _)) in H.
Qed.

Lemma unit_Bezout_mx m a b (k : 'I_m) : Bezout_mx a b k \in unitmx.
Proof.
rewrite /Bezout_mx; case:egcdrP=> g a1 b1 u v Huv Hg Ha1 Hb1.
have H: a1 * u - b1 * -v = 1; first by rewrite mulrN opprK.
by case: (mulmx1_unit (combine_mx_inv k H)).
Qed.

End Bezout_mx.

Section smith_def.

Variable R : euclidRingType.

Local Notation "''M_' ( m , n )" := 'M[R]_(m, n) : type_scope.
Local Notation "''M_' ( n )" := 'M[R]_(n, n) : type_scope.
Local Notation "''M_' n" := 'M[R]_(n, n) : type_scope.

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
and back to 1)

*)

Variable find1 : forall m n, 'M[R]_(m.+1,n.+1) -> R -> option 'I_m.

Arguments find1 {m n} _ _.

Hypothesis find1P : forall m n (A : 'M[R]_(1 + m,1 + n)) a,
  pick_spec [pred i | ~~(a %| A (rshift 1 i) 0)] (find1 A a).

Variable find2 :
  forall m n, 'M[R]_(m.+1,n.+1) -> R -> option ('I_(1 + m) * 'I_n).

Arguments find2 {m n} _ _.

Hypothesis find2P : forall m n (A : 'M[R]_(1 + m,1 + n)) a,
  pick_spec [pred ij | ~~(a %| A ij.1 (rshift 1 ij.2))] (find2 A a).

Fixpoint improve_pivot_rec k {m n} : 'M_(1 + m) -> 'M_(1 + m, 1 + n) -> 'M_(1 + n) ->
    'M_(1 + m) * 'M_(1 + m, 1 + n) * 'M_(1 + n) :=
  match k with
  | 0 => fun L A R => (L,A,R)
  | p.+1 => fun L A R =>
    let a := A 0 0 in
      if find1 A a is Some i then
        let L := Bezout_step (A 0 0) (A (rshift 1 i) 0) L i in
        let A := Bezout_step (A 0 0) (A (rshift 1 i) 0) A i in
        improve_pivot_rec p L A R
      else let u := dlsubmx A in let vA := ursubmx A in
      let vL := usubmx L in
      let u' := map_mx (fun x => 1 - odflt 0 (x %/? a)) u in
      let L := col_mx (usubmx L) (u' *m vL + dsubmx L) in
      let A := block_mx a%:M vA (const_mx a) (u' *m vA + drsubmx A) in
      if find2 A a is Some ij then
        let A := xrow 0 ij.1 A in
        let L := xrow 0 ij.1 L in
        let R := (Bezout_step (A 0 0) (A 0 (rshift 1 ij.2)) R^T ij.2)^T in
        let A := (Bezout_step (A 0 0) (A 0 (rshift 1 ij.2)) A^T ij.2)^T in
        improve_pivot_rec p L A R
      else (L, A, R)
  end.

Section improve_pivot_correct.

Variables m n : nat.

CoInductive improve_pivot_rec_spec L M R :
  'M_(1 + m) * 'M_(1 + m,1 + n) * 'M_(1 + n) -> Type :=
  ImprovePivotRecSpec L' A R' of L^-1 *m M *m R^-1 = L'^-1 *m A *m R'^-1
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & L' \in unitmx & R' \in unitmx
  : improve_pivot_rec_spec L M R (L',A,R').

Lemma unitrmxE k (M : 'M_k.+1) : (M \is a GRing.unit) = (M \in unitmx).
Proof. by []. Qed.

Definition unitmxEE := (unitmx_mul, unitmx_tr, unit_Bezout_mx,
  unitmx_perm).

Lemma improve_pivot_recP : forall k (L : 'M_(1 + m)) (M : 'M_(1 + m,1 + n)) R,
  (enorm (M 0%R 0%R) <= k)%N -> M 0 0 != 0 ->
    L \in unitmx -> R \in unitmx ->
    improve_pivot_rec_spec L M R (improve_pivot_rec k L M R).
Proof.
elim=> [L M R0|k IHk L M R0 Hk nzM00 unitL unitR /=].
  by rewrite leqn0 ; move/eqP/enorm_eq0 -> ; rewrite eqxx.
case: find1P=> [i Hi|Hi].
  have [||||L' A' R'] // := IHk.
  + by rewrite -ltnS; apply:(leq_trans (ltn_enorm nzM00 (sdvd_Bezout_step Hi)) Hk).
  + by rewrite -eqdr0 (congr_eqd (Bezout_step_mx00 M) (eqdd _)) eqdr0 gcdr_eq0 (negbTE nzM00).
  + by rewrite Bezout_stepE !unitmxEE.
  move=> HA' ? ? Hdiv HL' HR'; constructor=> //.
  * rewrite -HA' !Bezout_stepE invrM ?unit_Bezout_mx // !mulmxA.
    by congr (_ *m _ *m _); rewrite -mulmxA mulVmx ?unit_Bezout_mx // mulmx1.
  * rewrite (eqd_dvd (eqdd _) (Bezout_step_mx00 _)) in Hdiv.
    exact:(dvdr_trans Hdiv (dvdr_gcdl _ _)).
(*  by rewrite unitmx_mul HL' unit_Bezout_mx. *)
set P := map_mx _ _.
have Hblock: (block_mx 1 0 P 1%:M) *m M = block_mx (M 0 0)%:M (ursubmx M)
     (const_mx (M 0 0)) (P *m ursubmx M + drsubmx M).
  rewrite -{1}[M]submxK mulmx_block.
  rewrite !mul0mx !mul1mx !addr0 [ulsubmx M]mx11_scalar 2!mxE !lshift0.
  congr block_mx.
  rewrite mul_mx_scalar.
  apply/matrixP=> p q; rewrite ord1 !mxE lshift0 mulrBr mulr1.
  case:odivrP=> [d ->|]; first by rewrite mulrC subrK.
  by case/dvdrP:(negbFE (Hi p))=> x -> /(_ x); rewrite eqxx.
have unit_block : block_mx 1 0 P 1%:M \in unitmx.
  by rewrite unitmxE (det_lblock 1 P) !det1 mul1r unitr1.
have HblockL: (block_mx 1 0 P 1%:M) *m L =
  col_mx (usubmx L) (P *m usubmx L + dsubmx L).
  by rewrite -{1}[L]vsubmxK mul_block_col !mul1mx mul0mx addr0.
case: find2P=> [[i j]|Hij] /=.
  set B := block_mx _ _ _ _; set A := xrow _ _ B => Hij.
  have HMA: M 0 0 = A^T 0 0.
    rewrite /A /B -{4}(lshift0 n 0) !mxE tpermL.
    by case:splitP=> [i' _|i' Hi']; rewrite ?ord1 row_mxEl mxE ?eqxx.
  rewrite HMA in nzM00 Hk Hij.
  rewrite -[A]trmxK [A^T^T^T]trmxK ![A^T^T _ _]mxE.
  case: IHk => [||||L' A' R'].
  + rewrite -ltnS mxE; apply:(leq_trans _ Hk); apply:(ltn_enorm nzM00).
    apply: sdvd_Bezout_step.
    by rewrite {2}/A [_ (rshift _ _) _]mxE [xrow _ _ _ _ _]mxE tpermL.
  + by rewrite mxE -eqdr0 (congr_eqd (Bezout_step_mx00 _) (eqdd _)) eqdr0 gcdr_eq0 (negbTE nzM00).
  + by rewrite xrowE -HblockL !unitmxEE unit_block.
  + by rewrite !Bezout_stepE !unitmxEE.
  move => HA' ? ? Hdiv HL' HR'; constructor=> //.
    rewrite -HA' ![(A^T) 0 _]mxE /A /B -Hblock -HblockL !xrowE.
    rewrite !Bezout_stepE !trmx_mul !trmxK !invrM //.
    - rewrite !mulmxA -[_ / _ *m _]mulmxA mulVmx ?unitmx_perm // mulmx1.
      rewrite -[_ / _ *m _]mulmxA.
      rewrite mulVmx // mulmx1 -[_ *m _^T *m _]mulmxA.
      by rewrite mulmxV ?unitmx_tr ?unit_Bezout_mx // mulmx1.
    - by rewrite unitmx_tr unit_Bezout_mx.
    - by rewrite unitmx_perm.
    by rewrite !unitmxEE unit_block.
  apply: (dvdr_trans Hdiv); rewrite mxE (eqd_dvd (Bezout_step_mx00 _) (eqdd _)) HMA.
  exact: dvdr_gcdl.
constructor=> //.
+ by rewrite -HblockL -Hblock invrM // mulmxA mulmxKV.
+ rewrite -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N => i j.
  rewrite -{3}(lshift0 m 0) -{3}(lshift0 n 0) block_mxEul mxE eqxx !mxE.
(* Why do we have to specify all these arguments? *)
  case:splitP=> i' Hi'; rewrite !mxE; case:splitP=> j' Hj'; rewrite ?mxE ?ord1 //.
    by move:(negbFE (Hij (lshift m 0,j'))); rewrite block_mxEur !mxE.
  by move:(negbFE (Hij (rshift 1 i',j'))); rewrite block_mxEdr !mxE.
+ rewrite -[m.+1]/(1 + m)%N => i.
  rewrite -{5}(lshift0 m 0) -{3 6}(lshift0 n 0).
  rewrite (block_mxEul (M 0 0)%:M (ursubmx M)) !mxE.
  by case:splitP=> i' _; rewrite row_mxEl !mxE ?ord1.
+ rewrite -{3}(lshift0 m 0) -{3}(lshift0 n 0).
  by rewrite (block_mxEul (M 0 0)%:M (ursubmx M)) mxE dvdrr.
+ by rewrite -HblockL unitmx_mul unitmxE (det_lblock 1 P) !det1 mulr1 unitr1.
Qed.

Definition improve_pivot k (M : 'M_(1 + m, 1 + n)) :=
  improve_pivot_rec k 1%:M M 1%:M.

CoInductive improve_pivot_spec M :
  'M_(1 + m) * 'M_(1 + m,1 + n) * 'M_(1 + n) -> Type :=
  ImprovePivotSpec L A R of L *m M *m R = A
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & L \in unitmx & R \in unitmx
  : improve_pivot_spec M (L,A,R).

Lemma improve_pivotP k (M : 'M_(1 + m, 1 + n)) :
  (enorm (M 0%R 0%R) <= k)%N -> M 0 0 != 0 ->
  improve_pivot_spec M (improve_pivot k M).
Proof.
move=> ? ?; rewrite /improve_pivot.
have [||||L0 A R0] := improve_pivot_recP; rewrite ?unitmx1 //.
rewrite !invr1 mul1mx mulmx1 => eqM ? ? ? ? ?.
by constructor=> //; rewrite eqM !mulmxA mulmxV // mul1mx mulmxKV.
Qed.

End improve_pivot_correct.

Variable find_pivot :
  forall m n, 'M[R]_(m.+1,n.+1) -> option ('I_(1 + m) * 'I_(1 + n)).

Hypothesis find_pivotP : forall m n (A : 'M[R]_(1 + m,1 + n)),
  pick_spec [pred ij | A ij.1 ij.2 != 0] (find_pivot A).

Fixpoint Smith {m n} : 'M_(m,n) -> 'M_(m) * seq R * 'M_(n) :=
  match m, n return 'M_(m, n) -> 'M_(m) * seq R * 'M_(n) with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
      if [pick ij | A ij.1 ij.2 != 0] is Some (i, j) then
      let a := A i j in let A := xrow i 0 (xcol j 0 A) in
      (* this is where Euclidean norm eases termination argument *)
      let:(L,A,R) := improve_pivot (enorm a) A in 
      let a := A 0 0 in
      let u := dlsubmx A in let v := ursubmx A in
      let v' := map_mx (fun x => odflt 0 (x %/? a)) v in
      let A := (drsubmx A) - (const_mx 1 *m v) in
      let:(L', d, R') := Smith (map_mx (fun x => odflt 0 (x %/? a)) A) in
      (lift0_mx L' *m block_mx 1 0 (-const_mx 1) 1%:M *m (xcol i 0 L),
       a :: [seq x * a | x <- d],
       (xrow j 0 R) *m block_mx 1 (-v') 0 1%:M *m lift0_mx R')
    else (1%:M, [::], 1%:M)
  | _, _ => fun A => (1%:M, [::], 1%:M)
  end.

(*****************************)
Lemma size_Smith m n (A :'M_(m,n)) : 
  let: (_, d, _) := Smith A in (size d <= minn m n)%N.
Proof.
elim: m n A=>[n|m Ih n]; first by rewrite min0n.
case: n=>[|n A /=]; first by rewrite minn0.
case: pickP=> [[x1 x2] Hx|//].
case: (improve_pivot _ _); case => a b c /=.
case H: (Smith _)=>[[i j] k].
rewrite /= size_map minnSS ltnS.
by rewrite -/(let: (_,j,_) := (i,j,k) in (size j <= minn m n)%N) -H Ih.
Qed.
(*****************************)

(* Smith_spec is parametrized by R so that it can be used for PIDs as well *)
CoInductive Smith_spec {R : dvdRingType} {m n} M 
  : 'M[R]_m * seq R * 'M[R]_n -> Type :=
    SmithSpec L0 d R0 of L0 *m M *m R0 = diag_mx_seq m n d
                       & sorted (@dvdr R) d
                       & L0 \in unitmx 
                       & R0 \in unitmx : @Smith_spec R _ _ M (L0, d, R0).

Lemma SmithP : forall (m n : nat) (M : 'M_(m,n)), Smith_spec M (Smith M).
Proof.
elim=> [n M|m IHn]; first constructor; rewrite ?unitmx1 //.
  rewrite [M]flatmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case:(i == j :> nat).
case=> [M|n M /=]; first constructor; rewrite ?sorted_nil ?mxE ?unitmx1 //.
  rewrite [M]thinmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case:(i == j :> nat).
case:pickP=>[[i j] HMij | H].
  case:improve_pivotP; rewrite ?mxE ?tpermR ?leqnn //.
  rewrite -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N => L A R0 HA Hdiv HAi0 HA00.
  set A' := map_mx _ _; set v' := map_mx _ _.
  case:IHn=> L' d R' Hd Hsorted HL' HR' HL HR.
  constructor.
  * rewrite xcolE xrowE -!mulmxA (mulmxA M) -xcolE (mulmxA (tperm_mx _ _)).
    rewrite -xrowE (mulmxA L) (mulmxA _ R0) HA mulmx_block !mulmxA mulmx_block.
    rewrite -{1}(submxK A) !mulmx_block.
    do 2! rewrite !mul0mx !mulmx0 !mulmx1 !mul1mx !addr0 ?add0r.
    have Hu: const_mx 1 *m ulsubmx A = dlsubmx A.
      rewrite [ulsubmx A]mx11_scalar mul_mx_scalar.
      apply/matrixP=> k l.
      by rewrite ord1 !mxE mulr1 !lshift0 !HAi0.
    have Hv': (ulsubmx A *m v') = ursubmx A.
      apply/matrixP=> k l.
      rewrite (ord1 k) !mxE big_ord_recl big_ord0 !mxE !lshift0 addr0.
      case:odivrP=>[x ->|H]; first by rewrite mulrC.
      by case/dvdrP:(Hdiv 0 (rshift 1 l))=> q; move/eqP; rewrite (negbTE (H q)).
    rewrite diag_mx_seq_cons.
(*    rewrite mulmx_block !mulmx0 !mul0mx addr0 !add0r. *)
    congr block_mx.
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
      have Hdiv': forall i j, A 0 0 %| (drsubmx A - const_mx 1 *m ursubmx A) i j.
        move=> k l; rewrite !mxE big_ord1 !mxE mul1r.
        by apply:dvdr_sub; exact:Hdiv.
      have->: A 0 0 *: A' = drsubmx A - const_mx 1 *m ursubmx A.
        apply/matrixP=> k l; rewrite 2!mxE.
        case:odivrP=>[x ->|H]; first by rewrite mulrC.
        by case/dvdrP:(Hdiv' k l)=> q; move/eqP; rewrite (negbTE (H q)).
      by rewrite mulmxA.
    rewrite Hd; apply/matrixP=> k l; rewrite !mxE.
    case:(k == l :> nat); last by rewrite mulr0.
    have [Hk|Hk] := (ltnP k (size d)).
      by rewrite (nth_map 0 _ _ Hk) mulrC.
    by rewrite !nth_default ?size_map ?Hk // mulr0.
  * have {HA00}HA00: A 0 0 != 0.
      by apply/eqP=> H; move:HA00; rewrite H dvd0r (negbTE HMij).
    rewrite /= path_min_sorted; last by move=> a /mapP [b _ ->]; exact:dvdr_mull.
    case: d Hsorted {Hd} => //= a d; elim: d a=> //= a1 d IHd a0 /andP[a01 /IHd].
    by rewrite dvdr_mul2r ?a01.
  * rewrite xcolE !unitmx_mul unitmx_perm HL !unitmxE.
    by rewrite !det_lblock !det1 mul1r mulr1 unitr1 -unitmxE !andbT.
  * rewrite xrowE !unitmx_mul unitmx_perm HR !unitmxE.
   by rewrite 2!det_ublock 2!det1 2!mul1r unitr1 -unitmxE.
constructor =>[|||]; rewrite ?mxE ?unitmx1 //.
rewrite mul1mx mulmx1; apply/matrixP=> i j; rewrite !mxE (eqP (negbFE (H (i,j)))).
by case:(i == j :> nat); rewrite ?nth_nseq ?if_same nth_nil.
Qed.

End smith_def.

(* Section bench. *)

(* Open Scope Z_scope. *)

(* Definition d4 := [:: [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-2)%Z]; *)
(*            [:: 0%Z; 0%Z; 3%Z; 0%Z; 3%Z; 1%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-6)%Z; 0%Z; 0%Z;  *)
(*               (-6)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-3)%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 3%Z; 1%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-6)%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 3%Z; 1%Z; 0%Z; 0%Z; (-1)%Z; 0%Z; 0%Z; 1%Z; 2%Z;  *)
(*               (-1)%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 3%Z; 2%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-6)%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 4%Z]]. *)

(* Definition d5 := [:: [:: (-3)%Z; 1%Z; (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 4%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 4%Z; 2%Z; (-9)%Z; (-3)%Z; 0%Z; 0%Z;  *)
(*               (-6)%Z; 9%Z]; *)
(*            [:: 0%Z; (-3)%Z; (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 4%Z; 0%Z; *)
(*                0%Z; 4%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-4)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                (-9)%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-10)%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-5)%Z; 1%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-2)%Z;  *)
(*               (-4)%Z; 4%Z; 0%Z; 0%Z; 0%Z; 2%Z; 4%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-3)%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-10)%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 2%Z; 4%Z; (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-2)%Z; 1%Z;  *)
(*               (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; *)
(*                0%Z; (-3)%Z; 2%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-2)%Z;  *)
(*               (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; *)
(*                0%Z; 2%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 1%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 3%Z; 6%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; (-2)%Z; (-4)%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                (-2)%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-1)%Z; (-2)%Z; 0%Z; 2%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; *)
(*                3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-6)%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;  *)
(*               (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                (-3)%Z; 0%Z; 0%Z; 0%Z; 4%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z;  *)
(*               (-2)%Z; 2%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 1%Z;  *)
(*               (-4)%Z]; *)
(*            [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; *)
(*                0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]]. *)

(* Fixpoint Zegcd_rec (a b : Z) n {struct n} : Z * Z := *)
(*   if n is n'.+1 then *)
(*     if Z.eqb b 0 then (1, 0) else *)
(*     let: (u, v) := Zegcd_rec b (a mod b) n' in *)
(*       (v, (u - v * (a / b))) *)
(*   else (1, 0). *)

(* Definition Zegcd (a b : Z) := *)
(*   let (u,v) := Zegcd_rec a b (Zabs_nat b) in *)
(*   let g := a * u + b * v in *)
(*   (g,u,v,a/g,b/g). *)

(* Definition Zodvd (a b : Z) := Some (a / b). *)

(* Instance Zdvd : Refinements.Op.dvd Z := fun a b => (Z.eqb (b mod a) 0). *)

(* Definition I n := scalar_seqmx n 1%C. *)

(* Definition test := [:: [:: 4; 2; 2]; [:: 2; 8; 2]]. *)

(* Definition res_test := Smith_seqmx Z Zegcd Zodvd Zabs_nat test. *)

(* Definition res_test_mx := (mulseqmx 2 3 res_test.1.1 (mulseqmx 3 3 test res_test.2))%C. *)

(* Eval vm_compute in res_test.1.2. *)

(* (* *)
(* Definition M := drsubseqmx 1 1 res_test_mx. *)

(* Definition pivot_test := improve_pivot_seqmx Z Zegcd Zodvd res_test.1.1 M res_test.2 14. *)
(* *) *)


(* Definition res_d4 := Smith_seqmx Z Zegcd Zodvd Zabs_nat d4. *)
(* Definition res_d5 := Smith_seqmx Z Zegcd Zodvd Zabs_nat d5. *)

(* Eval vm_compute in (mulseqmx 23 46 res_d5.1.1 (mulseqmx 46 46 d5 res_d5.2))%C. (* true *) *)


(* Definition res_d5 := improve_pivot_seqmx Z Zegcd Zodvd 10 d5. *)

(* Definition test := [:: [:: 4; 4]; [:: 2; 8]]. *)

(* Definition res_test := improve_pivot_seqmx Z Zegcd Zodvd 10 test. *)

(* Eval compute in res_test.1.2. *)

(* Eval compute in mulseqmx 2 2 res_test.1.1 (mulseqmx 2 2 test res_test.2). *)

(* Eval compute in size (head [::] res_d5.2). (* 46 *) *)
(* Eval compute in size res_d5.2. (* 46 *) *)
(* Eval compute in size (head [::] d5). (* 46 *) *)
(* Eval compute in size d5. (* 23 *) *)
(* Eval compute in size (head [::] res_d5.1.1). (* 23 *) *)

(* Eval compute in (res_d5.1.2 == mulseqmx 23 46 res_d5.1.1 (mulseqmx 46 46 d5 res_d5.2))%C. (* true *) *)

(* End bench. *)
