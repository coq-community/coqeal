(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
(* Require Import ZArith. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg ssrint ssrnum fintype.
Require Import dvdring matrix mxalgebra bigop zmodp perm mxstructure.
Require Import refinements seqmatrix edr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory AlgOp.

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

Variable A : Type.

Import Refinements.Op.

Local Open Scope hetero_computable_scope.
Local Open Scope computable_scope.

Variable mxA : nat -> nat -> Type.
Variable ordA : nat -> Type.

Notation "''M[A]_' ( m , n )" := (mxA m n)
  (at level 8, format "''M[A]_' ( m ,  n )").
Notation "''M[A]_' ( n )" := (mxA n n) (at level 8, only parsing).
Notation "''I_' n" := (ordA n) : type_scope.

(* Pivoting functions *)
Variable find1 : forall m n, 'M[A]_(m.+1,n.+1) -> A -> option 'I_m.
Variable find2 :
  forall m n, 'M[A]_(m.+1,n.+1) -> A -> option ('I_(1 + m) * 'I_n).
Variable find_pivot :
  forall m n, 'M[A]_(1 + m,1 + n) -> option ('I_(1 + m) * 'I_(1 + n)).

Variable Bezout_step :
  A -> A -> forall m n, 'M[A]_(1+m,1+n) -> 'I_m -> 'M[A]_(m.+1,1+n).

Context `{zero A, one A, sub A, mul A, odvd A, enorm_of A}.
Context `{ulsub mxA, ursub mxA, dlsub mxA, drsub mxA, usub mxA, dsub mxA}.
Context `{block mxA, col_mx_class mxA}.
Context `{!hzero mxA, !hone mxA, !hopp mxA, !hadd mxA, !hsub mxA, !hmul mxA}.
Context `{!transpose_class mxA, xrow_class ordA mxA, xcol_class ordA mxA}.
Context `{forall n, zero (ordA (1 + n)), lift0_class ordA}.
Context `{fun_of A ordA mxA, cast_class A (mxA 1 1), const_mx_class A mxA}.
Context `{map_mx_class A mxA, lift0mx_class mxA}.

Fixpoint improve_pivot_rec k {m n} :
  'M[A]_(1 + m) -> 'M[A]_(1 + m, 1 + n) -> 'M[A]_(1 + n) ->
  'M[A]_(1 + m) * 'M[A]_(1 + m, 1 + n) * 'M[A]_(1 + n) :=
  match k with
  | 0 => fun P M Q => (P,M,Q)
  | p.+1 => fun P M Q =>
      let a := fun_of_matrix M 0 0 in
      if find1 M a is Some i then
        let Mi0 := fun_of_matrix M (lift0 i) 0 in
        let P := Bezout_step a Mi0 P i in
        let M := Bezout_step a Mi0 M i in
        improve_pivot_rec p P M Q
      else
      let u  := dlsubmx M in let vM := ursubmx M in let vP := usubmx P in
      let u' := map_mx (fun x => 1 - odflt 0 (x %/? a)) u in
      let P  := col_mx (usubmx P) (u' *m vP + dsubmx P)%HC in
      let M  := block_mx (cast_op a) vM
                         (const_mx a) (u' *m vM + drsubmx M)%HC in
      if find2 M a is Some (i,j) then
        let M := xrow 0 i M in let P := xrow 0 i P in
        let a := fun_of_matrix M 0 0 in
        let M0ij := fun_of_matrix M 0 (lift0 j) in
        let Q := (Bezout_step a M0ij Q^T j)^T in
        let M := (Bezout_step a M0ij M^T j)^T in
        improve_pivot_rec p P M Q
      else (P, M, Q)
  end.

Definition improve_pivot k m n (M : 'M[A]_(1 + m, 1 + n)) :=
  improve_pivot_rec k 1%HC M 1%HC.

(* TODO: Why is this so slow?? *)
Fixpoint Smith m n : 'M[A]_(m,n) -> 'M[A]_(m) * seq A * 'M[A]_(n) :=
  match m, n with
  | _.+1, _.+1 => fun M : 'M[A]_(1 + _, 1 + _) =>
      if find_pivot M is Some (i, j) then
      let a := fun_of_matrix M i j in let M := xrow i 0 (xcol j 0 M) in
      (* this is where Euclidean norm eases termination argument *)
      let: (P,M,Q) := improve_pivot (enorm_op a) M in
      let a  := fun_of_matrix M 0 0 in
      let u  := dlsubmx M in let v := ursubmx M in
      let v' := map_mx (fun x => odflt 0 (x %/? a)) v in
      let M  := ((drsubmx M) - (const_mx 1%C *m v))%HC in
      let: (P', d, Q') := Smith (map_mx (fun x => odflt 0 (x %/? a)) M) in
      ((lift0_mx P' *m block_mx 1 0 (- const_mx 1%C) 1 *m (xcol i 0 P)%C)%HC,
       a :: [seq x * a | x <- d],
       ((xrow j 0 Q)%C *m block_mx 1 (- v') 0 1 *m lift0_mx Q')%HC)
    else (1%HC, [::], 1%HC)
  | _, _ => fun M => (1%HC, [::], 1%HC)
  end.

End smith_def.

Section smith_theory.

Import Refinements.Op.

Variable E : euclidDomainType.

Local Notation "''M_' ( m , n )" := 'M[E]_(m, n) : type_scope.
Local Notation "''M_' ( n )" := 'M[E]_(n, n) : type_scope.
Local Notation "''M_' n" := 'M[E]_(n, n) : type_scope.

Variable find1 : forall m n, 'M[E]_(m.+1,n.+1) -> E -> option 'I_m.
Variable find2 : forall m n, 'M[E]_(m.+1,n.+1) -> E -> option ('I_(1+m) * 'I_n).
Variable find_pivot :
  forall m n, 'M[E]_(1 + m,1 + n) -> option ('I_(1 + m) * 'I_(1 + n)).

Hypothesis find1P : forall m n (A : 'M[E]_(1 + m,1 + n)) a,
  pick_spec [pred i | ~~(a %| A (lift 0 i) 0)] (find1 A a).
Hypothesis find2P : forall m n (A : 'M[E]_(1 + m,1 + n)) a,
  pick_spec [pred ij | ~~(a %| A ij.1 (lift 0 ij.2))] (find2 A a).
Hypothesis find_pivotP : forall m n (A : 'M[E]_(1 + m,1 + n)),
  pick_spec [pred ij | A ij.1 ij.2 != 0] (find_pivot A).

Instance : zero E := 0%R.
Instance : one E := 1%R.
Instance : sub E := subr.
Instance : mul E := fun x y => x * y.
Instance : odvd E := fun x y => x %/? y.
Instance : enorm_of E := fun x => enorm x.

Instance : ulsub (matrix E) := @matrix.ulsubmx E.
Instance : ursub (matrix E) := @matrix.ursubmx E.
Instance : dlsub (matrix E) := @matrix.dlsubmx E.
Instance : drsub (matrix E) := @matrix.drsubmx E.
Instance : usub (matrix E)  := @matrix.usubmx E.
Instance : dsub (matrix E)  := @matrix.dsubmx E.
Instance : block (matrix E) := @matrix.block_mx E.
Instance : col_mx_class (matrix E) := @matrix.col_mx E.

Instance : hzero (matrix E) := fun m n => 0 : 'M[E]_(m,n).
Instance : hone (matrix E) := fun n => 1%:M : 'M[E]_n.
Instance : hopp (matrix E) := @oppmx E.
Instance : hadd (matrix E) := @addmx E.
Instance : hsub (matrix E) := fun m n (M N : 'M[E]_(m,n)) => M - N.
Instance : hmul (matrix E) := @mulmx E.

Instance : transpose_class (matrix E) := @matrix.trmx E.
Instance : xrow_class ordinal (matrix E) := @matrix.xrow E.
Instance : xcol_class ordinal (matrix E) := @matrix.xcol E.

Instance : forall n, zero 'I_(1 + n) := fun n => 0%R.
Instance : lift0_class ordinal := fun n (i : 'I_n) => lift 0 i.

Instance : fun_of E ordinal (matrix E) := @matrix.fun_of_matrix E.
Instance : cast_class E (matrix E 1 1) := fun a => a%:M.
Instance : const_mx_class E (matrix E) := @matrix.const_mx E.

Instance : map_mx_class E (matrix E) := @matrix.map_mx E E.
Instance : lift0mx_class (matrix E) := @matrix.lift0_mx E.

CoInductive improve_pivot_rec_spec m n P M Q :
  'M_(1 + m) * 'M_(1 + m,1 + n) * 'M_(1 + n) -> Type :=
  ImprovePivotQecSpec P' M' Q' of P^-1 *m M *m Q^-1 = P'^-1 *m M' *m Q'^-1
  & (forall i j, M' 0 0 %| M' i j)
  & (forall i, M' i 0 = M' 0 0)
  & M' 0 0 %| M 0 0
  & P' \in unitmx & Q' \in unitmx
  : improve_pivot_rec_spec P M Q (P',M',Q').

Lemma unitrmxE k (M : 'M_k.+1) : (M \is a GRing.unit) = (M \in unitmx).
Proof. by []. Qed.

Definition unitmxEE := (unitmx_mul, unitmx_tr, unit_Bezout_mx, unitmx_perm).

Definition improve_pivot_recR := improve_pivot_rec find1 find2 (@Bezout_step E).

Lemma improve_pivot_recP :
  forall k m n (P : 'M_(1 + m)) (M : 'M_(1 + m,1 + n)) Q,
  (enorm (M 0%R 0%R) <= k)%N -> M 0 0 != 0 ->
   P \in unitmx -> Q \in unitmx ->
    improve_pivot_rec_spec P M Q (improve_pivot_recR k P M Q).
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
  apply/matrixP=> p q; rewrite ord1 !mxE lshift0 mulrBr mulr1 !rshift1; simpC.
  case: odivrP=> [d ->|]; first by rewrite mulrC subrK.
  by case/dvdrP:(negbFE (Hi p))=> x -> /(_ x); rewrite eqxx.
have unit_block : matrix.block_mx 1 0 P 1%:M \in unitmx
  by rewrite unitmxE (det_lblock 1 P) !det1 mul1r unitr1.
have HblockL : (matrix.block_mx 1 0 P 1%:M) *m L =
  matrix.col_mx (matrix.usubmx L) (P *m matrix.usubmx L + matrix.dsubmx L)
  by rewrite -{1}[L]vsubmxK mul_block_col !mul1mx mul0mx addr0.
case: find2P=> [[i j]|Hij] /=; simpC.
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
  'M_(1 + m) * 'M_(1 + m,1 + n) * 'M_(1 + n) -> Type :=
  ImprovePivotSpec L A R of L *m M *m R = A
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & L \in unitmx & R \in unitmx
  : improve_pivot_spec M (L,A,R).

Lemma improve_pivotP k m n (M : 'M_(1 + m, 1 + n)) :
  (enorm (M 0%R 0%R) <= k)%N -> M 0 0 != 0 ->
  improve_pivot_spec M (improve_pivot find1 find2 (@Bezout_step E) k M).
Proof.
move=> ? ?; rewrite /improve_pivot.
have := (@improve_pivot_recP k _ _ 1%:M M 1%:M).
rewrite /improve_pivot_recR=> [[]] //; rewrite ?unitmx1 //.
rewrite !invr1 mul1mx mulmx1 => ? ? ? eqM ? ? ? ? ?.
by constructor=> //; rewrite eqM !mulmxA mulmxV // mul1mx mulmxKV.
Qed.

Lemma SmithP : forall (m n : nat) (M : 'M_(m,n)),
  smith_spec M (Smith find1 find2 find_pivot (@Bezout_step E) M).
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
  simpC; rewrite /hmul_op /hmul_instance_0. (* Why is this necessary? *)
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
      transitivity (A 0 0 *: (L' *m A' *m R')).
      rewrite -[_ *m A' *m _]mulmxA scalemxAr scalemxAl.
      have Hdiv' : forall i j, A 0 0 %| (matrix.drsubmx A - matrix.const_mx 1 *m matrix.ursubmx A) i j.
        by move=> k l; rewrite !mxE big_ord1 !mxE mul1r dvdr_sub ?Hdiv.
      have -> : A 0 0 *: A' = matrix.drsubmx A - matrix.const_mx 1 *m matrix.ursubmx A.
        apply/matrixP=> k l; rewrite 2!mxE.
        simpC; case: odivrP=>[x ->|H]; first by rewrite mulrC.
        by case/dvdrP:(Hdiv' k l)=> q /eqP; rewrite (negbTE (H q)).
      by rewrite mulmxA.
    rewrite Hd; apply/matrixP=> k l; rewrite !mxE.
    case: (k == l :> nat); last by rewrite mulr0.
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
by case: (i == j :> nat); rewrite ?nth_nseq ?if_same nth_nil.
Qed. (* Why is this so slow??? *)

Lemma size_Smith m n (A : 'M_(m,n)) :
  let: (_, d, _) := (Smith find1 find2 find_pivot (@Bezout_step E) A) in (size d <= minn m n)%N.
Proof.
elim: m n A=>[n'|m' Ih n']; first by rewrite min0n.
case: n'=>[|n' A /=]; first by rewrite minn0.
case: find_pivotP=> [[x1 x2] Hx|//].
case: (improve_pivot _ _); case => a b c /=.
case H: (Smith _)=>[[i j] k].
rewrite /= size_map minnSS ltnS.
by rewrite -/(let: (_,j,_) := (i,j,k) in (size j <= minn m' n')%N) -H Ih.
Qed.

Definition euclidEDRMixin := EDR.Mixin SmithP.
Canonical euclidEDRType   := Eval hnf in EDRType E euclidEDRMixin.

Section smith_param.
(* TODO: Write this *)
End smith_param.
End smith_theory.

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
