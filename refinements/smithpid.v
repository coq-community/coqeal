(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
(* Require Import ZArith. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg ssrint ssrnum fintype.
Require Import dvdring matrix mxalgebra bigop zmodp perm mxstructure.
Require Import refinements seqmatrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory AlgOp.

Local Open Scope ring_scope.

(* Preliminary section on Bezout matrices *)
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
  let k' := lift 0 k in
  let d := \row_j (a *+ (j == 0) + d *+ (j == k') + ((j != 0) && (j != k'))%:R) in
  diag_mx d + c *: delta_mx k' 0 + b *: delta_mx 0 k'.

Definition combine_step (a b c d : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :=
  let k' := lift 0 k in
  let r0 := a *: row 0 M + b *: row k' M in
  let rk := c *: row 0 M + d *: row k' M in
  \matrix_i (r0 *+ (i == 0) + rk *+ (i == k') + row i M *+ ((i != 0) && (i != k'))).

Definition Bezout_mx (a b : R) (m : nat) (k : 'I_m) :=
  let:(_,u,v,a1,b1) := egcdr a b in combine_mx u v (-b1) a1 k.

Definition Bezout_step (a b : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :=
  let:(_,u,v,a1,b1) := egcdr a b in combine_step u v (-b1) a1 M k.

Lemma combine_stepE (a b c d : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
  combine_step a b c d M k = combine_mx a b c d k *m M.
Proof.
apply/matrixP=> i j; have [g u v a' b' _ _ _ _] := egcdrP a b.
rewrite !mxE (bigD1 ord0) // !mxE (bigD1 (lift 0 k)) // !mxE /=.
case H: (i == 0).
  rewrite big1=> [|l /andP [/negbTE H1 /negbTE H2]].
    by rewrite (eqP H) !eqxx !mulr1n !mxE !mulr0 !addr0 mulr0n add0r mulr1.
  by rewrite !mxE (eqP H) (eq_sym 0 l) H1 H2 mulr0n !mulr0 !add0r mul0r.
case H': (i == lift 0 k).
  rewrite big1=> [|l /andP [/negbTE H1 /negbTE H2]].
    by rewrite (eqP H') !(eqxx,mulr1n,mxE,mulr0,addr0,mulr1,mulr0n,add0r).
  by rewrite !mxE (eqP H') !(eq_sym _ l) eqxx H1 H2 mulr0n !mulr0 !add0r mul0r.
rewrite (bigD1 i); last by rewrite H H'.
rewrite !mxE big1=> [/=|l /andP [/andP [/negbTE H1 /negbTE H2] /negbTE H3]].
  by rewrite H H' eqxx !(mulr0n,mulr0,mulr1n,addr0,mul0r,add0r,mul1r).
by rewrite !mxE H H' H1 H2 (eq_sym i l) H3 mulr0n !mulr0 !addr0 mul0r.
Qed.

Lemma combine_mx_inv (a b c d : R) m (k : 'I_m) :
  a * d - b * c = 1 ->
  combine_mx a b c d k *m combine_mx d (-b) (-c) a k = 1%:M.
Proof.
move=> H; rewrite -combine_stepE; apply/matrixP=> i j; rewrite !mxE.
case Hi: (i == 0).
  rewrite !mxE (eqP Hi) !eqxx !mulr0 mxE !addr0 (eq_sym 0 j).
  case Hj: (j == 0); first by rewrite (eqP Hj) mulr1 !mulr0 addr0 sub0r mulrN.
  rewrite !mulr0 !add0r addr0 (eq_sym _ j).
  case: (j == lift 0 k); last by rewrite !mulr0 add0r.
  by rewrite mulr1 mulr1n mulrN mulrC addNr.
case Hj: (j == 0).
  rewrite !mxE (eqP Hj) Hi add0r.
  case Hk: (i == _); last by rewrite !mxE Hi Hk eqxx !add0r !mulr0 addr0.
  by rewrite !mxE !eqxx !mulr0 mulr1 !addr0 !add0r mulrN addrC mulrC addNr.
case Hk: (i == _); last by rewrite !mxE Hi Hj Hk !mulr0 !add0r !addr0.
rewrite !mxE (eq_sym 0 j) Hj (eqP Hk) !(eqxx,mulr0,addr0,add0r) (eq_sym _ j).
case: (j == lift 0 k); last by rewrite !mulr0 addr0.
by rewrite !mulr1 addrC mulrN (mulrC c) (mulrC d).
Qed.

Lemma Bezout_stepE a b (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
  Bezout_step a b M k = Bezout_mx a b k *m M.
Proof.
rewrite /Bezout_step /Bezout_mx; have [g u v a' b' _ _ _ _] := egcdrP.
by rewrite combine_stepE.
Qed.

Lemma Bezout_step_mx00 m n (M : 'M_(1 + m,1 + n)) {k : 'I_m} :
 (Bezout_step (M 0 0) (M (lift 0 k) 0) M k) 0 0 %= gcdr (M 0 0) (M (lift 0 k) 0).
Proof.
rewrite /Bezout_step; have [g u v a' b' Bezout_a'b' gcd_g H1 H2] := egcdrP.
by rewrite !mxE !addr0 {1}H1 {1}H2  !mulrA -mulrDl Bezout_a'b' mul1r.
Qed.

(* We need to generalize and use an equality for the correctness proof of
improve_pivot_rec to go through (otherwise we cannot do an induction on the
accessibility proof) *)
Lemma sdvd_Bezout_step (m n : nat) a (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
 a = M 0 0 -> ~~ (a %| M (lift 0 k) 0) ->
 (Bezout_step a (M (lift 0 k) 0) M k) 0 0 %<| a.
Proof.
move=> -> H; rewrite /sdvdr (eqd_dvd (Bezout_step_mx00 _) (eqdd _)) dvdr_gcdl.
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

Variable A : priRingType.

Variable find1 : forall m n, 'M[A]_(m.+1,n.+1) -> A -> option 'I_m.
Variable find2 :
  forall m n, 'M[A]_(m.+1,n.+1) -> A -> option ('I_(1 + m) * 'I_n).

Hypothesis find1P : forall m n (A : 'M[A]_(1 + m,1 + n)) a,
  pick_spec [pred i | ~~(a %| A (lift 0 i) 0)] (find1 A a).
Hypothesis find2P : forall m n (A : 'M[A]_(1 + m,1 + n)) a,
  pick_spec [pred ij | ~~(a %| A ij.1 (lift 0 ij.2))] (find2 A a).

(* This lemma is used in the termination proof of improve_pivot_rec *)
Lemma sdvd_Bezout_step2 m n a ij u' vA (M : 'M[A]_(1 + m, 1 + n)) :
  a = M 0 0 ->
  let B : 'M_(1 + m, 1 + n) := block_mx a%:M vA (const_mx a) (u' *m vA + drsubmx M) in
  let C := xrow 0 ij.1 B in
  ~~ (a %| B ij.1 (lift 0 ij.2)) ->
  (Bezout_step (C 0 0) (C 0 (lift 0 ij.2)) C^T ij.2)^T 0 0 %<| a.
Proof.
move=> ->.
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

Fixpoint improve_pivot_rec {m n} a (L : 'M[A]_(1 + m)) (M : 'M[A]_(1 + m, 1 + n))
         (R : 'M[A]_(1 + n)) (eq_a : a = M 0 0) (k : Acc (@sdvdr A) a) :
         'M[A]_(1 + m) * 'M[A]_(1 + m, 1 + n) * 'M[A]_(1 + n) :=
    match k with Acc_intro IHa =>
    (* let a := M 0 0 in *)
      if find1P M a is Pick i Hi then
        let Ai0 := M (lift 0 i) 0 in 
        let L := Bezout_step a Ai0 L i in 
        let A : 'M_(1 + m, 1 + n) := Bezout_step a Ai0 M i in
        @improve_pivot_rec m n _ L A R (erefl _) (IHa _ (sdvd_Bezout_step eq_a Hi))
      else
      let u  := dlsubmx M in let vA := ursubmx M in let vL := usubmx L in
      let u' := map_mx (fun x => 1 - odflt 0 (x %/? a)) u in
      let L  := col_mx (usubmx L) (u' *m vL + dsubmx L) in
      let A  := block_mx a%:M vA
                         (const_mx a) (u' *m vA + drsubmx M) in
      if find2P A a is Pick ij Hij then
        let A := xrow 0 ij.1 A in let L := xrow 0 ij.1 L in
        let a := fun_of_matrix A 0 0 in 
        let A0ij := fun_of_matrix A 0 (lift 0 ij.2) in 
        let R := (Bezout_step a A0ij (R^T) ij.2)^T in
        let A := (Bezout_step a A0ij (A^T) ij.2)^T in
        @improve_pivot_rec m n _ L A R (erefl _) (IHa _ (sdvd_Bezout_step2 eq_a Hij))
      else (L, A, R)
    end.

Variable find_pivot :
  forall m n, 'M[A]_(1 + m,1 + n) -> option ('I_(1 + m) * 'I_(1 + n)).

Definition improve_pivot m n (M : 'M[A]_(1 + m, 1 + n)) :=
  improve_pivot_rec 1 1 (erefl _) (sdvdr_wf (M 0 0)).

Fixpoint Smith {m n} : 'M[A]_(m,n) -> 'M[A]_(m) * seq A * 'M[A]_(n) :=
  match m, n return 'M[A]_(m, n) -> 'M[A]_(m) * seq A * 'M[A]_(n) with
  | _.+1, _.+1 => fun A : 'M[A]_(1 + _, 1 + _) =>
      if find_pivot A is Some (i, j) then
      let a := fun_of_matrix A i j in let A := xrow i 0 (xcol j 0 A) in
      let: (L,A,R) := improve_pivot A in
      let a  := fun_of_matrix A 0 0 in
      let u  := dlsubmx A in let v := ursubmx A in
      let v' := map_mx (fun x => odflt 0 (x %/? a)) v in
      let A  := ((drsubmx A) - (const_mx 1 *m v)) in
      let: (L', d, R') := Smith (map_mx (fun x => odflt 0 (x %/? a)) A) in
      ((lift0_mx L' *m block_mx 1%:M 0 (- const_mx 1) 1%:M *m (xcol i 0 L)),
       a :: [seq x * a | x <- d],
       (xrow j 0 R *m block_mx 1 (- v') 0 1%:M *m lift0_mx R'))
    else (1, [::], 1)
  | _, _ => fun A => (1%:M, [::], 1%:M)
  end.

Hypothesis find_pivotP : forall m n (A : 'M[A]_(1 + m,1 + n)),
  pick_spec [pred ij | A ij.1 ij.2 != 0] (find_pivot A).

CoInductive improve_pivot_rec_spec m n L M R :
  'M[A]_(1 + m) * 'M[A]_(1 + m,1 + n) * 'M[A]_(1 + n) -> Type :=
  ImprovePivotRecSpec L' A R' of L^-1 *m M *m R^-1 = L'^-1 *m A *m R'^-1
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & L' \in unitmx & R' \in unitmx
  : improve_pivot_rec_spec L M R (L',A,R').

Lemma unitrmxE k (M : 'M[A]_k.+1) : (M \is a GRing.unit) = (M \in unitmx).
Proof. by []. Qed.

Definition unitmxEE := (unitmx_mul, unitmx_tr, unit_Bezout_mx, unitmx_perm).

Scheme Acc_rect_dep := Induction for Acc Sort Type.

Lemma improve_pivot_recP : 
  forall m n a (L : 'M_(1 + m)) (M : 'M_(1 + m,1 + n)) R (eq_a : a = M 0 0) (k : Acc (@sdvdr A) a),
   M 0 0 != 0 ->
   L \in unitmx -> R \in unitmx ->
    improve_pivot_rec_spec L M R (improve_pivot_rec L R eq_a k).
Proof.
move=> m n a L M R eq_a k.
elim/Acc_rect_dep: k M L R eq_a => a' Acc_a' IHa' M L R eq_a nzM00 unitL unitR /=.
(*
elim=> [m n L M R0|k IHk m n L M R0 Hk nzM00 unitL unitR /=].
  by rewrite leqn0 => /eqP /enorm_eq0 ->; rewrite eqxx.
*)
case: find1P=> [i Hi|Hi].
  have [|||L' A' R' HA' ? ? Hdiv HL' HR'] // := IHa'; do ?constructor => //.
(*  + by rewrite -ltnS (leq_trans (ltn_enorm nzM00 (sdvd_Bezout_step Hi)) Hk). *)
  + by rewrite eq_a -eqdr0 (congr_eqd (Bezout_step_mx00 M) (eqdd _)) eqdr0 gcdr_eq0
               (negbTE nzM00).
  + by rewrite Bezout_stepE !unitmxEE.
  + rewrite -HA' !Bezout_stepE invrM ?unit_Bezout_mx // !mulmxA.
    by congr (_ *m _ *m _); rewrite -mulmxA mulVmx ?unit_Bezout_mx // mulmx1.
  + rewrite eq_a (eqd_dvd (eqdd _) (Bezout_step_mx00 _)) in Hdiv.
    exact: (dvdr_trans Hdiv (dvdr_gcdl _ _)).
set P := map_mx _ _.
have Hblock : (matrix.block_mx 1 0 P 1%:M) *m M = 
               matrix.block_mx (M 0 0)%:M (matrix.ursubmx M)
              (matrix.const_mx (M 0 0)) (P *m matrix.ursubmx M + matrix.drsubmx M).
  rewrite -{1}[M]submxK mulmx_block !mul0mx !mul1mx !addr0
          [matrix.ulsubmx M]mx11_scalar 2!mxE !lshift0.
  congr matrix.block_mx; rewrite mul_mx_scalar.
  apply/matrixP=> p q; rewrite ord1 !mxE lshift0 mulrBr mulr1 !rshift1; simpC.
  case: odivrP=> [d ->|]; first by rewrite eq_a mulrC subrK.
  by case/dvdrP:(negbFE (Hi p))=> x -> /(_ x); rewrite eqxx.
have unit_block : matrix.block_mx 1 0 P 1%:M \in unitmx
  by rewrite unitmxE (det_lblock 1 P) !det1 mul1r unitr1.
have HblockL : (matrix.block_mx 1 0 P 1%:M) *m L =
  matrix.col_mx (matrix.usubmx L) (P *m matrix.usubmx L + matrix.dsubmx L)
  by rewrite -{1}[L]vsubmxK mul_block_col !mul1mx mul0mx addr0.
case: find2P=> [[i j]|Hij] /=; simpC.
  set B := matrix.block_mx _ _ _ _; set C := matrix.xrow _ _ B => Hij.
  have HMA: M 0 0 = C^T 0 0.
    rewrite /C /B -{2}(lshift0 n 0) !mxE tpermL.
    by case: splitP=> [i' _|i' Hi']; rewrite ?ord1 row_mxEl mxE ?eqxx.
  rewrite HMA in nzM00.
  case: IHa' => [|||L' A' R' HA' ? ? Hdiv HL' HR']; do ?constructor=> //.
(*  + rewrite -ltnS mxE (leq_trans _ Hk) ?(ltn_enorm nzM00) ?sdvd_Bezout_step //.
    by rewrite {2}/A [_ (lift _ _) _]mxE [matrix.xrow _ _ _ _ _]mxE tpermL. *)
  + rewrite -[C]trmxK [C^T^T^T]trmxK ![C^T^T _ _]mxE.
by rewrite mxE -eqdr0 (congr_eqd (Bezout_step_mx00 _) (eqdd _)) eqdr0
               gcdr_eq0 (negbTE nzM00).
  + by rewrite xrowE -HblockL !unitmxEE unit_block.
  + by rewrite !Bezout_stepE !unitmxEE.
  + rewrite -HA' -[C]trmxK [C^T^T^T]trmxK ![C^T^T _ _]mxE.
    rewrite ![(C^T) 0 _]mxE /C /B eq_a -Hblock -HblockL !xrowE.
    rewrite !Bezout_stepE !trmx_mul !trmxK !invrM //.
    - rewrite !mulmxA -[_ / _ *m _]mulmxA mulVmx ?unitmx_perm // mulmx1.
      rewrite -[_ / _ *m _]mulmxA mulVmx // mulmx1 -[_ *m _^T *m _]mulmxA.
      by rewrite mulmxV ?unitmx_tr ?unit_Bezout_mx // mulmx1.
    - by rewrite unitmx_tr unit_Bezout_mx.
    - by rewrite unitmx_perm.
    by rewrite !unitmxEE unit_block.
  rewrite -[C]trmxK [C^T^T^T]trmxK ![C^T^T _ _]mxE in Hdiv.
  rewrite (dvdr_trans Hdiv) // mxE (eqd_dvd (Bezout_step_mx00 _) (eqdd _)) HMA.
  exact: dvdr_gcdl.
constructor=> //; first by rewrite eq_a -HblockL -Hblock invrM // mulmxA mulmxKV.
+ rewrite -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N => i j.
  rewrite eq_a -{3}(lshift0 m 0) -{3}(lshift0 n 0) block_mxEul mxE eqxx !mxE.
(* Why do we have to specify all these arguments? *)
  case: splitP=> i' Hi'; rewrite mxE; case: splitP=> j' Hj'; rewrite ?mxE ?ord1 //.
    by move: (negbFE (Hij (lshift m 0,j'))); rewrite eq_a -rshift1 block_mxEur !mxE.
  by move: (negbFE (Hij (lift 0 i',j'))); rewrite eq_a -!rshift1 block_mxEdr !mxE.
+ rewrite -[m.+1]/(1 + m)%N => i.
  rewrite eq_a -{5}(lshift0 m 0) -{3 6}(lshift0 n 0) (block_mxEul (M 0 0)%:M _) !mxE.
  by case: splitP=> i' _; rewrite row_mxEl !mxE ?ord1.
+ rewrite eq_a -{3}(lshift0 m 0) -{3}(lshift0 n 0).
  by rewrite (block_mxEul (M 0 0)%:M (matrix.ursubmx M)) mxE dvdrr.
by rewrite -HblockL unitmx_mul unitmxE (det_lblock 1 P) !det1 mulr1 unitr1.
Qed.

CoInductive improve_pivot_spec m n M :
  'M[A]_(1 + m) * 'M[A]_(1 + m,1 + n) * 'M[A]_(1 + n) -> Type :=
  ImprovePivotSpec L A R of L *m M *m R = A
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & L \in unitmx & R \in unitmx
  : improve_pivot_spec M (L,A,R).

Lemma improve_pivotP m n (M : 'M_(1 + m, 1 + n)) :
  M 0 0 != 0 -> improve_pivot_spec M (improve_pivot M).
Proof.
move=> ?; rewrite /improve_pivot.
have := (@improve_pivot_recP _ _ _ 1%:M M 1%:M (erefl _) (sdvdr_wf _)).
case; rewrite ?unitmx1 // !invr1 mul1mx mulmx1 => ? ? ? eqM ? ? ? ? ?.
by constructor=> //; rewrite eqM !mulmxA mulmxV // mul1mx mulmxKV.
Qed.

(* Smith_spec is parametrized by R so that it can be used for PIDs as well *)
CoInductive Smith_spec {R : dvdRingType} {m n} M
  : 'M[R]_m * seq R * 'M[R]_n -> Type :=
    SmithSpec L0 d R0 of L0 *m M *m R0 = diag_mx_seq m n d
                       & sorted (@dvdr R) d
                       & L0 \in unitmx
                       & R0 \in unitmx : @Smith_spec R _ _ M (L0, d, R0).

Lemma SmithP : forall (m n : nat) (M : 'M_(m,n)), 
  Smith_spec M (Smith M).
Proof.
elim=> [n M|m IHn]; first constructor; rewrite ?unitmx1 //.
  rewrite [M]flatmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case: (i == j :> nat).
case=> [M|n M /=]; first constructor; rewrite ?sorted_nil ?mxE ?unitmx1 //.
  rewrite [M]thinmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case: (i == j :> nat).
case: find_pivotP =>[[i j] HMij | H].
  case: improve_pivotP; rewrite ?mxE ?tpermR ?leqnn //.
  rewrite -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N => L B R0 HB Hdiv HAi0 HA00.
  set A' := map_mx _ _; set v' := map_mx _ _.
  case: IHn=> L' d R' Hd Hsorted HL' HR' HL HR; constructor.
  * rewrite xcolE xrowE -!mulmxA (mulmxA M) -xcolE (mulmxA (tperm_mx _ _)).
    rewrite -xrowE (mulmxA L) (mulmxA _ R0) HB mulmx_block !mulmxA mulmx_block.
    rewrite -{1}(submxK B) !mulmx_block.
    do 2! rewrite !mul0mx !mulmx0 !mulmx1 !mul1mx !addr0 ?add0r.
    have Hu: matrix.const_mx 1 *m matrix.ulsubmx B = matrix.dlsubmx B.
      rewrite [matrix.ulsubmx B]mx11_scalar mul_mx_scalar; apply/matrixP=> k l.
      by rewrite ord1 !mxE mulr1 !lshift0 !HAi0.
    have Hv': (matrix.ulsubmx B *m v') = matrix.ursubmx B.
      apply/matrixP=> k l.
      rewrite (ord1 k) !mxE big_ord_recl big_ord0 !mxE !lshift0 addr0.
      simpC; case: odivrP=>[x ->|H]; first by rewrite mulrC.
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
      transitivity (B 0 0 *: (L' *m A' *m R')).
      rewrite -[_ *m A' *m _]mulmxA scalemxAr scalemxAl.
      have Hdiv' : forall i j, B 0 0 %| (matrix.drsubmx B - matrix.const_mx 1 *m matrix.ursubmx B) i j.
        by move=> k l; rewrite !mxE big_ord1 !mxE mul1r dvdr_sub ?Hdiv.
      have -> : B 0 0 *: A' = matrix.drsubmx B - matrix.const_mx 1 *m matrix.ursubmx B.
        apply/matrixP=> k l; rewrite 2!mxE.
        simpC; case: odivrP=>[x ->|H]; first by rewrite mulrC.
        by case/dvdrP:(Hdiv' k l)=> q /eqP; rewrite (negbTE (H q)).
      by rewrite mulmxA.
    rewrite Hd; apply/matrixP=> k l; rewrite !mxE.
    case: (k == l :> nat); last by rewrite mulr0.
    have [Hk|Hk] := (ltnP k (size d)).
      by rewrite (nth_map 0 _ _ Hk) mulrC.
    by rewrite !nth_default ?size_map ?Hk // mulr0.
  * have {HA00}HA00: B 0 0 != 0.
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
by rewrite -/(let: (_,j,_) := (i,j,k) in (size j <= minn m' n')%N) -H Ih.
Qed.

End smith_def.