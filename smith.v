(*
Formalization of Anders' Haskell algorithm
for general Smith Normal form
using ssreflect matrices
*)
Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg ssrint ssrnum fintype.
Require Import dvdring matrix mxalgebra bigop zmodp perm mxstructure.
Require Import refinements seqmatrix.
Require Import binint_direct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section smith_def.

Local Open Scope ring_scope.

Variable R : euclidRingType.

Local Notation "''M_' ( m , n )" := 'M[R]_(m, n) : type_scope.
Local Notation "''M_' ( n )" := 'M[R]_(n, n) : type_scope.
Local Notation "''M_' n" := 'M[R]_(n, n) : type_scope.

Definition combine_step (a b c d : R) (m n : nat) (M : 'M_(m,n)) k l :=
  let rk := a *: row k M + b *: row l M in
  let rl := c *: row k M + d *: row l M in
  \matrix_i (rk *+ (i == k) + rl *+ (i == l) + row i M *+ ((i != k) && (i != l))).

Definition combine_mx (a b c d : R) (m : nat) (k l : 'I_m) :=
  let d := \row_j (a *+ (j == k) + d *+ (j == l) + ((j != k) && (j != l))%:R) in
  diag_mx d + c *: delta_mx l k + b *: delta_mx k l.

(*
Definition bz_mx_inv (a b : R) (m : nat) (k : 'I_m) :=
  let:(g,u,v,a1,b1) := egcdr a b in
  let k' := rshift 1 k in
  let d := \row_j (a1 *+ (j == 0) + u *+ (j == k') + ((j != 0) && (j != k'))%:R) in
  diag_mx d + b1 *: delta_mx k' 0 - v *: delta_mx 0 k'.
*)

(*
Definition bz_mx (a b : R) (m : nat) (k : 'I_m) : 'M_(1+m) :=
  let:(g,u,v,a1,b1) := egcdr a b in
  let d := \row_(j < m) (1 *+ (j != k) + a1 *+ (j == k)) in
  block_mx (a%:M) (-b1 *: delta_mx 0 k) (v *: delta_mx k 0) (diag_mx d).
*)



(* Local Close Scope ring_scope. *)

Import GRing.Theory.

Lemma combine_stepE (a b c d : R) (m n : nat) (M : 'M_(m, n)) (k l : 'I_m) :
  combine_step a b c d M k l = combine_mx a b c d k l *m M.
Proof. admit. Qed.

(* Try to rewrite without case analysis *)
Lemma combine_mx_inv (a b c d : R) m (k l : 'I_m) :
  a * d - b * c = 1 ->
  combine_mx a b c d k l *m combine_mx d (-b) (-c) a k l = 1%:M.
Proof. admit. Qed.


(*****************
  if the following Bezout identity holds: u * a1 + v * b1 = 1,
  bz_mx a b n k represents the following matrix (dots are zeros):
    
          (kth column)
  / u .... v ..... \
  | . 1 .......... |
  | ....1......... |
  | -b1 .. a1 .... | (kth row)
  | ..........1... |
  \ .............1 /


  (determinant is +/-1)
******************)

Definition Bezout_step (a b : R) (m n : nat) (M : 'M_(m,n)) k l :=
  let:(_,u,v,a1,b1) := egcdr a b in
  combine_step u v (-b1) a1 M k l.

Definition Bezout_mx (a b : R) (m : nat) (k l : 'I_m) :=
  let:(_,u,v,a1,b1) := egcdr a b in
  combine_mx u v (-b1) a1 k l.

(*
Lemma Bezout_step_diag {m n : nat} {M : 'M_(m, n)} (k : 'I_m) (k' : 'I_n) l :
  k = k' :> nat ->
  Bezout_step (M k k') (M l k') M k l k k' %= gcdr (M k k') (M l k').
Proof.
move=> eq_kk'.
rewrite /Bezout_step.
case:egcdrP=> g u v a1 b1 Hg Hgcd H1 H2.
rewrite !mxE eqxx !mxE addr0.
set T := _ 0 k'.
have->: T = 0.
rewrite /T.
move: H1.
have [->|] := altP (k =P l); last by rewrite mxE.
rewrite !mxE.
rewrite {1}H2.
*)


Lemma bz_mx_00 {m n : nat} {M : 'M_(1 + m,1 + n)} {k : 'I_m} :
 (bz_mx (M 0 0) (M (rshift 1 k) 0) m k *m M) 0 0 %= gcdr (M 0 0) (M (rshift 1 k) 0).
Proof.
rewrite /bz_mx; case:egcdrP=> g u v a1 b1 Hg Hgcd H1 H2.
by rewrite combine_mxE !mxE !addr0 {1}H1 {1}H2 !mulrA -mulrDl Hg mul1r.
Qed.

Lemma sdvd_bz_mx (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
 ~~ (M 0 0 %| M (rshift 1 k) 0) ->
 (bz_mx (M 0 0) (M (rshift 1 k) 0) m k *m M) 0 0 %<| M 0 0.
Proof.
move=> H ; rewrite /sdvdr (eqd_dvd (bz_mx_00) (eqdd _)) dvdr_gcdl.
rewrite (eqd_dvd (eqdd _ ) (bz_mx_00)).
by apply/negP=> H'; rewrite (dvdr_trans H' (dvdr_gcdr _ _)) in H.
Qed.

(*
Lemma bz_mx_invP (a b : R) m k : bz_mx a b m k *m bz_mx_inv a b m k = 1%:M.
Proof.
rewrite bz_mxE /bz_mx_inv.
apply/matrixP=> i j; rewrite !mxE.
case:egcdrP=> g u v a1 b1 Huv Hg Ha Hb /=.
case Hi:(i==0).
  case Hj:(j==0).
    rewrite !mxE (eqP Hi) (eqP Hj) !mulr1n !mulr0n !eqxx.
    rewrite mxE !mulr0 !addr0 add0r !subr0 mulr1.
    admit.
  rewrite !mxE (eqP Hi) !mulr1n !mulr0n !eqxx.
  rewrite mxE !mulr0 !addr0 add0r !subr0 mulr1.

rewrite /bz_mx /bz_mx_inv.
*)

Lemma unit_bz_mx m n (M : 'M_(1 + m,1 + n)) k :
  (bz_mx (M 0 0) (M (rshift 1 k) 0) m k) \in unitmx.
Proof.
rewrite /bz_mx; case:egcdrP=> g a1 b1 u v Huv Hg Ha1 Hb1.
have H: a1 * u - b1 * -v = 1; first by rewrite mulrN opprK.
by case:(mulmx1_unit (combine_mx_inv _ _ _ _ m k H)).
Qed.

Local Open Scope ring_scope.

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

Fixpoint improve_pivot k {m n} : 'M_(1 + m, 1 + n) -> 'M_(1 + m) * 'M_(1 + m, 1 + n) * 'M_(1 + n) :=
  match k with
  | 0 => fun A => (1%:M,A,1%:M)
  | p.+1 => fun A =>
    let a := A 0 0 in
      if find1 A a is Some i then
        let L := bz_mx (A 0 0) (A (rshift 1 i) 0) m i in
        let A := L *m A in
        let:(L',A,R') := improve_pivot p A in
        (L' *m L, A, R')
      else let u := dlsubmx A in let v := ursubmx A in
      let u' := map_mx (fun x => 1 - odflt 0 (x %/? a)) u in
      let L := block_mx 1 0 u' 1%:M in
      let A := block_mx a%:M v (const_mx a) (drsubmx A + u' *m v) in
      if find2 A a is Some ij then
        let A := xrow 0 ij.1 A in
        let R := (bz_mx (A 0 0) (A 0 (rshift 1 ij.2)) n ij.2)^T in
        let A := A *m R in
        let:(L',A,R') := improve_pivot p A in
        (L' *m xrow 0 ij.1 L, A, R *m R')
      else (L, A, 1%:M)
  end.

Section improve_pivot_correct.

Variables m n : nat.

CoInductive improve_pivot_spec M :
  'M_(1 + m) * 'M_(1 + m,1 + n) * 'M_(1 + n) -> Type :=
  ImprovePivotSpec L A R of L *m M *m R = (A : 'M_(1 + m, 1 + n))
  & (forall i j, A 0 0 %| A i j)
  & (forall i, A i 0 = A 0 0)
  & A 0 0 %| M 0 0
  & L \in unitmx & R \in unitmx
  : improve_pivot_spec M (L,A,R).

Lemma improve_pivotP : forall k (M : 'M_(1 + m,1 + n)),
  (enorm (M 0%R 0%R) <= k)%N -> M 0 0 != 0 ->
    improve_pivot_spec M (improve_pivot k M).
Proof.
elim=> [M|k IHk M Hk H /=].
  by rewrite leqn0 ; move/eqP/enorm_eq0 -> ; rewrite eqxx.
case: find1P=> [i Hi|Hi].
  case:(IHk (_ *m M))=> [||L' A' R'].
  + by rewrite -ltnS; apply:(leq_trans (ltn_enorm H (sdvd_bz_mx _ _ _ _ Hi)) Hk).
  + by rewrite -eqdr0 (congr_eqd bz_mx_00 (eqdd _)) eqdr0 gcdr_eq0 (negbTE H).
  + rewrite mulmxA=> HA' ? ? Hdiv HL' HR'; constructor=> //.
      rewrite (eqd_dvd (eqdd _) bz_mx_00) in Hdiv.
      exact:(dvdr_trans Hdiv (dvdr_gcdl _ _)).
  by rewrite unitmx_mul HL' unit_bz_mx.
set P := map_mx _ _.
have Hblock: (block_mx 1 0 P 1%:M) *m M = block_mx (M 0 0)%:M (ursubmx M)
     (const_mx (M 0 0)) (drsubmx M + P *m ursubmx M).
  rewrite -{1}[M]submxK mulmx_block.
  rewrite !mul0mx !mul1mx !addr0 [ulsubmx M]mx11_scalar 2!mxE !lshift0.
  congr block_mx; last by rewrite addrC.
  rewrite mul_mx_scalar.
  apply/matrixP=> p q; rewrite ord1 !mxE lshift0 mulrBr mulr1.
  case:odivrP=> [d ->|]; first by rewrite mulrC subrK.
  by case/dvdrP:(negbFE (Hi p))=> x -> /(_ x); rewrite eqxx.
case: find2P=> [[i j]|Hij].
  set B := block_mx _ _ _ _; set A := xrow _ _ _=> Hij.
  rewrite -[A]trmxK -trmx_mul.
  have HMA: M 0 0 = A^T 0 0.
    rewrite /A /B -{4}(lshift0 n 0) !mxE tpermL.
    by case:splitP=> [i' _|i' Hi']; rewrite ?ord1 row_mxEl mxE ?eqxx.
  rewrite HMA in H Hk Hij.
  rewrite ![(A^T)^T 0 _]mxE.
  case:IHk=> [||L' A' R'].
  + rewrite -ltnS mxE; apply:(leq_trans _ Hk); apply:(ltn_enorm H).
    apply:sdvd_bz_mx.
    by rewrite {2}/A [_ (rshift _ _) _]mxE [xrow _ _ _ _ _]mxE tpermL.
  + by rewrite mxE -eqdr0 (congr_eqd bz_mx_00 (eqdd _)) eqdr0 gcdr_eq0 (negbTE H).
  + rewrite {1}trmx_mul mulmxA=> HA' ? ? Hdiv HL' HR'; constructor=> //.
    * rewrite -HA' ![(A^T) 0 _]mxE trmxK !mulmxA; congr mulmx; congr mulmx.
      by rewrite -mulmxA /A /B; congr mulmx; rewrite xrowE -mulmxA -xrowE Hblock.
    * apply:(dvdr_trans Hdiv); rewrite mxE (eqd_dvd bz_mx_00 (eqdd _)) HMA.
      exact:dvdr_gcdl.
    * rewrite xrowE !unitmx_mul HL' unitmx_perm unitmxE det_lblock !det1.
    by rewrite mul1r unitr1.
  by rewrite unitmx_mul HR' unitmx_tr unit_bz_mx.
constructor=> [|i j|i|||].
+ by rewrite Hblock mulmx1.
+ rewrite -{3}(lshift0 m 0) -{3}(lshift0 n 0) block_mxEul mxE eqxx !mxE.
  case:splitP=> i' Hi'; rewrite !mxE; case:splitP=> j' Hj'; rewrite ?mxE ?ord1 //.
    by move:(negbFE (Hij (lshift m 0,j'))); rewrite block_mxEur !mxE.
  by move:(negbFE (Hij (rshift 1 i',j'))); rewrite block_mxEdr !mxE.
+ rewrite -{5}(lshift0 m 0) -{3 6}(lshift0 n 0) block_mxEul !mxE.
  by case:splitP=> i' _; rewrite row_mxEl !mxE ?ord1.
+ by rewrite -(lshift0 m 0) -(lshift0 n 0) block_mxEul mxE dvdrr.
+ by rewrite unitmxE det_lblock !det1 mulr1 unitr1.
exact:unitmx1.
Qed.

End improve_pivot_correct.

Section improve_pivot_seqmx.

Variable A : Type.

Variable egcd : A -> A -> A * A * A * A * A.
Variable odvd : A -> A -> option A.

Import Refinements.Op.

Context `{add A, mul A, one A, zero A, dvd A, opp A, sub A}.

Definition combine_step_seqmx (a b c d : A) (M : seqmatrix A) k l :=
  let rk := nth [::] M k in
  let rl := nth [::] M l in
  let r'k := (scaleseqmx a [:: rk] + scaleseqmx b [:: rl])%C in
  let r'l := (scaleseqmx c [:: rk] + scaleseqmx d [:: rl])%C in
  mkseq (fun i => if i == k then head [::] r'k else if i == l then head [::] r'l else nth [::] M i) (size M).

Definition bz_step_seqmx (a b : A) (M : seqmatrix A) (k l : nat) : seqmatrix A :=
  let:(_,u,v,a1,b1) := egcd a b in combine_step_seqmx u v (-b1)%C a1 M k l.

Fixpoint find1_seqmx a i (M : seqmatrix A) {struct M} : option (nat * A) :=
  if M is s::M' then
    if (a %| head 0 s)%C then find1_seqmx a i.+1 M' else Some (i, head 0%C s)
  else None.

Fixpoint find2_seqmx_aux a j (r : seq A) {struct r} : option (nat * A) :=
  if r is x::r' then
    if (a %| x)%C then find2_seqmx_aux a j.+1 r' else Some (j, x)
  else None.

Fixpoint find2_seqmx a i (M : seqmatrix A) {struct M} : option (nat * nat * A) :=
    if M is s::M' then
      if find2_seqmx_aux a 0%N s is Some (j, x) then Some (i, j, x)
      else find2_seqmx a i.+1 M'
    else None.

Fixpoint improve_pivot_seqmx (L M R : seqmatrix A) k :=
  match k with
  | 0%N => (L,M,R)
  | p.+1 => 
    let a := head 0%C (head [::] M) in
    let m := size M in let mL := size L in let offset := (mL - m)%N in
    if find1_seqmx a 0%N M is Some (i, b) then
      let M := bz_step_seqmx a b M 0 i in
      let L := bz_step_seqmx a b L offset (offset + i) in
      improve_pivot_seqmx L M R p
    else let u := dlsubseqmx 1 1 M in let v := ursubseqmx 1 1 M in
    let u' := map_seqmx (fun x => 1 - odflt 0 (odvd x a))%C u in
    (* L needs to be updated here *)
    let n := size (head [::] M) in
    let M := block_seqmx (scalar_seqmx 1 a) v (const_seqmx m.-1 1 a) (drsubseqmx 1 1 M + mulseqmx 1 n.-1 u' v)%C in
    let vL := nth [::] L offset in
    let L := (L + mulseqmx 1 n (col_seqmx (const_seqmx offset.+1 1%N 0%C) u') [::vL])%C in
    if find2_seqmx a 0%N M is Some (i, j, x) then
      let M := xrowseqmx 0%N i M in
      let L := xrowseqmx offset (offset + i) L in
      let M := trseqmx (bz_step_seqmx a x (trseqmx M) 0 j) in
      let R := trseqmx (bz_step_seqmx a x (trseqmx R) (size R - n) (size R - n + j)) in
      improve_pivot_seqmx L M R p
    else (L,M,R)
  end.

End improve_pivot_seqmx.

Variable find_pivot :
  forall m n, 'M[R]_(m.+1,n.+1) -> option ('I_(1 + m) * 'I_(1 + n)).

Hypothesis find_pivotP : forall m n (A : 'M[R]_(1 + m,1 + n)),
  pick_spec [pred ij | A ij.1 ij.2 != 0] (find_pivot m n A).

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

CoInductive Smith_spec {m n} M : 'M[R]_m * seq R * 'M[R]_n -> Type :=
  SmithSpec L0 d R0 of L0 *m M *m R0 = diag_mx_seq m n d
  & sorted (@dvdr R) d
  & L0 \in unitmx & R0 \in unitmx : Smith_spec M (L0, d, R0).

Lemma SmithP : forall (m n : nat) (M : 'M_(m,n)), Smith_spec M (Smith M).
Proof.
elim=> [n M|m IHn]; first constructor; rewrite ?unitmx1 //.
  rewrite [M]flatmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case:(i == j :> nat).
case=> [M|n M]; first constructor; rewrite ?sorted_nil ?mxE ?unitmx1 //.
  rewrite [M]thinmx0 mulmx1 mul1mx; apply/matrixP=> i j; rewrite !mxE nth_nil.
  by case:(i == j :> nat).
rewrite /Smith -{1}/Smith.
case:pickP=>[[i j] HMij | H].
  case:improve_pivotP=> [||L A R0 HA Hdiv HAi0 HA00]; rewrite ?mxE ?tpermR ?leqnn //.
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
      by apply/eqP=> H; move:HA00; rewrite H dvd0r !mxE !tpermR (negbTE HMij).
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

Section Smith_seqmx.

Variable A : Type.

Variable egcd : A -> A -> A * A * A * A * A.
Variable odvd : A -> A -> option A.
Variable enorm : A -> nat.

Import Refinements.Op.

Context `{add A, mul A, one A, zero A, dvd A, opp A, sub A, eq A}.

Fixpoint find_pivot_seqmx_aux j (r : seq A) {struct r} : option (nat * A) :=
  if r is x::r' then
    if (x == 0)%C then find_pivot_seqmx_aux j.+1 r' else Some (j, x)
  else None.

Fixpoint find_pivot_seqmx i (M : seqmatrix A) {struct M} : option (nat * nat * A) :=
    if M is s::M' then
      if find_pivot_seqmx_aux 0%N s is Some (j, x) then Some (i, j, x)
      else find_pivot_seqmx i.+1 M'
    else None.

Fixpoint Smith_seqmx_rec m n (L M R : seqmatrix A) : seqmatrix A * seq A * seqmatrix A :=
  match m, n with
  | p.+1, q.+1 =>
    if find_pivot_seqmx 0 M is Some (i, j, a) then
      let offsety := size L - m in
      let offsetx := size R - n in
      let M := xrowseqmx i 0 (xcolseqmx j 0 M) in 
      let L := xrowseqmx (offsety + i) offsety L in
      let R := xcolseqmx (offsetx + j) offsetx R in
      let: (L,M,R) := improve_pivot_seqmx A egcd odvd L M R (enorm a) in
      let a := head 0%C (head [::] M) in
      let u := dlsubseqmx 1 1 M in let v := ursubseqmx 1 1 M in
      let v' := map_seqmx (fun x => odflt 0 (odvd x a))%C v in
      let M := (drsubseqmx 1 1 M - mulseqmx 1 q (const_seqmx p 1 1) v)%C in
      let vL := nth [::] L offsety in let mL := size L in
      let L' := mulseqmx 1 mL (col_seqmx (const_seqmx offsety.+1 1 0%C) (const_seqmx p 1 1%C)) [:: vL] in
      let L := (L - L')%C in
(*      let L := col_seqmx vL (dsubseqmx 1 L - L')%C in *)
      let uR := map (fun s => [:: nth 0%C s offsetx]) R in let nR := size R in
      let R' := mulseqmx 1 q uR (row_seqmx (const_seqmx 1 offsetx.+1 0%C) v') in
      let R := (R - R')%C in
      let: (L,d,R) := Smith_seqmx_rec p q L (map_seqmx (fun x => odflt 0 (odvd x a))%C M) R in
      (L, a :: [seq x * a | x <- d]%C, R)
    else
      (L, [::], R)
  | _, _ => (L, [::], R)
  end.

Definition Smith_seqmx (M : seqmatrix A) :=
  let m := size M in let n := size (head [::] M) in
  Smith_seqmx_rec m n (scalar_seqmx m 1%C) M (scalar_seqmx n 1%C).

(*
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
*)

End Smith_seqmx.

Section bench.

Open Scope Z_scope.

Definition d4 := [:: [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-2)%Z];
           [:: 0%Z; 0%Z; 3%Z; 0%Z; 3%Z; 1%Z; 0%Z; 0%Z; 0%Z; 
              (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-6)%Z; 0%Z; 0%Z; 
              (-6)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-3)%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 3%Z; 1%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-6)%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 3%Z; 1%Z; 0%Z; 0%Z; (-1)%Z; 0%Z; 0%Z; 1%Z; 2%Z; 
              (-1)%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 3%Z; 2%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-6)%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 4%Z]].

Definition d5 := [:: [:: (-3)%Z; 1%Z; (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 4%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 4%Z; 2%Z; (-9)%Z; (-3)%Z; 0%Z; 0%Z; 
              (-6)%Z; 9%Z];
           [:: 0%Z; (-3)%Z; (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 4%Z; 0%Z;
               0%Z; 4%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-4)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               (-9)%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-10)%Z; 0%Z; 0%Z; 0%Z; 
              (-5)%Z; 1%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-2)%Z; 
              (-4)%Z; 4%Z; 0%Z; 0%Z; 0%Z; 2%Z; 4%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-3)%Z; 0%Z; 0%Z; 0%Z; 
              (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-10)%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 2%Z; 4%Z; (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-2)%Z; 1%Z; 
              (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z;
               0%Z; (-3)%Z; 2%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-2)%Z; 
              (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z;
               0%Z; 2%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 1%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 3%Z; 6%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-1)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; (-2)%Z; (-4)%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               (-2)%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-2)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-1)%Z; (-2)%Z; 0%Z; 2%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z;
               3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; (-6)%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 
              (-3)%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               (-3)%Z; 0%Z; 0%Z; 0%Z; 4%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 2%Z; 0%Z; 0%Z; 0%Z; 0%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 
              (-2)%Z; 2%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 1%Z; 
              (-4)%Z];
           [:: 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z;
               0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z]].

Fixpoint Zegcd_rec (a b : Z) n {struct n} : Z * Z :=
  if n is n'.+1 then
    if Z.eqb b 0 then (1, 0) else
    let: (u, v) := Zegcd_rec b (a mod b) n' in
      (v, (u - v * (a / b)))
  else (1, 0).

Definition Zegcd (a b : Z) :=
  let (u,v) := Zegcd_rec a b (Zabs_nat b) in
  let g := a * u + b * v in
  (g,u,v,a/g,b/g).

Definition Zodvd (a b : Z) := Some (a / b).

Instance Zdvd : Refinements.Op.dvd Z := fun a b => (Z.eqb (b mod a) 0).

Definition I n := scalar_seqmx n 1%C.

Definition test := [:: [:: 4; 2; 2]; [:: 2; 8; 2]].

Definition res_test := Smith_seqmx Z Zegcd Zodvd Zabs_nat test.

Definition res_test_mx := (mulseqmx 2 3 res_test.1.1 (mulseqmx 3 3 test res_test.2))%C.

Eval vm_compute in res_test.1.2.

(*
Definition M := drsubseqmx 1 1 res_test_mx.

Definition pivot_test := improve_pivot_seqmx Z Zegcd Zodvd res_test.1.1 M res_test.2 14.
*)


Definition res_d4 := Smith_seqmx Z Zegcd Zodvd Zabs_nat d4.
Definition res_d5 := Smith_seqmx Z Zegcd Zodvd Zabs_nat d5.

Eval vm_compute in (mulseqmx 23 46 res_d5.1.1 (mulseqmx 46 46 d5 res_d5.2))%C. (* true *)


Definition res_d5 := improve_pivot_seqmx Z Zegcd Zodvd 10 d5.

Definition test := [:: [:: 4; 4]; [:: 2; 8]].

Definition res_test := improve_pivot_seqmx Z Zegcd Zodvd 10 test.

Eval compute in res_test.1.2.

Eval compute in mulseqmx 2 2 res_test.1.1 (mulseqmx 2 2 test res_test.2).

Eval compute in size (head [::] res_d5.2). (* 46 *)
Eval compute in size res_d5.2. (* 46 *)
Eval compute in size (head [::] d5). (* 46 *)
Eval compute in size d5. (* 23 *)
Eval compute in size (head [::] res_d5.1.1). (* 23 *)

Eval compute in (res_d5.1.2 == mulseqmx 23 46 res_d5.1.1 (mulseqmx 46 46 d5 res_d5.2))%C. (* true *)

End bench.