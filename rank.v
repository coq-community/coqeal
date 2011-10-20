Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import ssralg fintype perm.
Require Import matrix  bigop zmodp mxalgebra.
Require Import matrix_facts seqmatrix.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section FieldRank.
Variable K : fieldType.

Local Open Scope ring_scope.

Lemma rank0M': forall (n m:nat) (M: 'M[K]_(n,m)),
  \rank (row_mx (0: 'cV[K]_n) M) = \rank M.
Proof.
move => n m M.
have -> : row_mx 0 M = (col_mx 0 M^T)^T.
- by move => a; rewrite -[X in (col_mx X _)]trmx0 tr_col_mx !trmxK.
by rewrite mxrank_tr eqmxM0M mxrank_tr.
Qed.

Lemma tool_rank : forall n:nat, n != 0%N -> n <= 1 -> n = 1%N.
Proof. by case => [ | [ | n]]. Qed.

Lemma inv_scalar0 : forall n (a:K), a%:M = 0 :> 'M[K]_n.+1 -> a = 0.
Proof.
move => n a.
rewrite -scalemx1 => /matrixP  h.
by move: (h 0 0); rewrite !mxE mulr1.
Qed.

Lemma rank0M: forall (n m:nat) (M: 'M[K]_(n,m)),
  \rank (col_mx (0: 'rV[K]_m) M) = \rank M.
Proof. by move => n m M; rewrite eqmxM0M. Qed.

(* rank ( a    0 .... 0  )  = 1 + rank M if a != 0
          c1
          ...     M
          cn
*)
Lemma rankaM : forall (n m:nat) (M: 'M[K]_(n,m)) (a:K) (c:'cV[K]_n),
 a != 0 -> \rank (block_mx (a%:M) 0 c M) = (1 + \rank M)%N.
Proof.
move => n m M a c ha.
have: ((block_mx a%:M 0 c M)^T :=: (col_mx a%:M c)^T + (col_mx 0 M)^T)%MS.
- rewrite tr_block_mx !tr_col_mx /block_mx.
  apply eqmx_sym.
  by apply addsmxE.
have hC: (col_mx a%:M c) != 0.
- apply/negP; move/eqP => h.
  move/negP : ha; apply.
  move/colP : h => h.
  move: (h 0); rewrite !mxE.
  case: splitP => i hi //.
  by rewrite [i]ord1 !mxE /= mulr1n => ->.
rewrite -mxrank_tr => ->.
rewrite mxrank_disjoint_sum.
- rewrite rank_rV mxrank_tr rank0M.
  by rewrite -trmx_neq0 hC.
rewrite !tr_col_mx !tr_scalar_mx trmx0.
apply/eqP.
apply/rowV0P => v.
rewrite sub_capmx; case/andP.
case/sub_rVP => b hb.
case/submxP => B hB.
have : v 0 0 = 0 /\ v 0 0 = b * a.
- split.
  + rewrite hB !mxE big1 // => i _.
    rewrite !mxE.
    case: splitP => j //.
    by rewrite !mxE /= mulr0.
  rewrite hb !mxE.
  case: splitP => j //.
  by rewrite [j]ord1 !mxE /= mulr1n.
rewrite {3}hb; case => ->.
rewrite -[0](@mul0r _ a). move/(mulIf ha) <-.
by rewrite scale0r.
Qed.

Lemma rankaM' : forall (n m:nat) (M: 'M[K]_(n,m)) (a:K) (l:'rV[K]_m),
 a != 0 -> \rank (block_mx (a%:M) l 0 M) = (1 + \rank M)%N.
Proof.
move => n m M a l ha.
rewrite -mxrank_tr tr_block_mx tr_scalar_mx trmx0 rankaM //.
by rewrite mxrank_tr.
Qed.

Lemma tcast: forall p m:nat, (p + (1 + m))%N = (p.+1 + m)%N.
Proof.
by move => p m; rewrite addnA addn1.
Qed.

Fixpoint ssr_tool (n m p:nat) (vs: 'M[K]_(m,n)) {struct p}:
  'M[K]_(p, 1 + n) ->  ('M[K]_(p + m,n) * bool) :=
   match p return 'M[K]_(p, 1 + n) -> ('M[K]_(p + m, n) * bool) with
   | p'.+1 => fun (l : 'M_(1 + p', 1 + n)) =>
     let a := l 0 0 in
     if a == 0 then
       let: (R,b) := ssr_tool (col_mx (ursubmx l) vs) (dsubmx l)
         in (castmx (tcast p' m,refl_equal n) R,b)
     else
       let v := a^-1 *: dlsubmx l in
       let R := drsubmx l - v *m ursubmx l in
       let v0 : 'rV[K]_n := 0 in
         (castmx (tcast p' m,refl_equal n) (col_mx R (col_mx v0 vs)),
           true)
   | _ => fun l => (vs, false)
end.

Fixpoint ssr_rank (m n:nat) {struct n} : 'M[K]_(m,n) -> nat :=
  match n return 'M[K]_(m,n) -> nat with
   |  q.+1 => fun M => let:(R,b) := @ssr_tool _ 0%N _ 0 M in
     (b + ssr_rank R)%N
   | _ => fun _ => 0%N
end.


Lemma ssr_tool_col0 : forall p m n (vs: 'M[K]_(m,n)) (M: 'M[K]_(p, 1 + n)),
 let: (_,b) := ssr_tool vs M in
 if b then True else lsubmx M = 0.
Proof.
elim => [ m n vs M | p hi] /=.
- by rewrite [lsubmx M]flatmx0.
rewrite [p.+1]/(1 + p)%N => m n vs M /=.
case: ifP => hM00 //.
case: ssr_tool (hi _ _ (col_mx (ursubmx M) vs) (dsubmx M)) => R b.
case: ifP => hb // /colP h /=.
rewrite -[M]vsubmxK.
apply/colP => i; rewrite !mxE.
case: splitP => j.
- by rewrite [j]ord1 !mxE !lshift0 (eqP hM00).
by move: (h j); rewrite !mxE !rshift1.
Qed.

Lemma ssr_toolP : forall p m n (vs: 'M[K]_(m,n)) (M: 'M[K]_(p,1 + n)),
  let: (R,b) := ssr_tool vs M in
    if b then \rank ((row_mx 0 vs) + M)%MS = (1 + \rank R)%N
      else (R :=: vs + rsubmx M)%MS.
Proof.
elim => [ m n vs M | p hi] /=.
- rewrite [rsubmx M]flatmx0.
  apply eqmx_sym.
  by apply addsmx0.
rewrite [p.+1]/(1 + p)%N => m n vs M /=.
case: ifP => [hM00 | ].
case: ssr_tool (hi _ _ (col_mx (ursubmx M) vs) (dsubmx M)) => R b.
- case: ifP => hb hR.
  + rewrite eqmx_cast -hR.
    have -> :
      row_mx 0 (col_mx (ursubmx M) vs) = col_mx (usubmx M) (row_mx 0 vs).
    * rewrite -[usubmx M]hsubmxK [lsubmx (usubmx M)]mx11_scalar !mxE
        !lshift0 (eqP hM00) scalar0.
      by rewrite [X in _ = X]block_mxEh col_mx0.
    transitivity (\rank (row_mx 0 vs + (usubmx M + dsubmx M))).
    * apply adds_eqmx; first by apply eqmx_refl.
      rewrite -{1}[M]vsubmxK; apply eqmx_sym.
      by apply addsmxE.
    rewrite addsmxA.
    apply adds_eqmx; last by apply eqmx_refl.
    rewrite addsmxC.
    by apply addsmxE.
  apply (eqmx_trans (eqmx_cast _ _)).
  apply (eqmx_trans hR).
  apply (eqmx_trans (adds_eqmx (eqmx_sym (addsmxE (ursubmx M) vs))
                               (eqmx_refl _))).
  rewrite [(_ + vs)%MS]addsmxC -addsmxA.
  apply adds_eqmx; first by apply eqmx_refl.
  apply (eqmx_trans (addsmxE (ursubmx M) (drsubmx M))).
  rewrite -{3}[M]vsubmxK -[usubmx M]hsubmxK -[dsubmx M]hsubmxK.
  rewrite [col_mx (row_mx _ _) (row_mx _ _)]block_mxEh row_mxKr.
  by apply eqmx_refl.
rewrite eqmx_cast.
move/negbT => hM00.
rewrite addsmxE.
set D : 'M[K]_(1 + p) :=
  block_mx 1%:M 0 (-1 / M 0 0 *: (dlsubmx M)) 1%:M.
have hD : row_full (block_mx (1%:M : 'M[K]_m) 0 0 D).
- by rewrite row_full_unit unitmxE !det_lblock !det1 !mul1r unitr1.
rewrite -(eqmxMfull (col_mx (row_mx 0 vs) M) hD) -{1}[M]submxK
  [ulsubmx M]mx11_scalar !mxE !lshift0 block_mxEh mul_row_col.
rewrite !mul_col_mx !mul1mx !mul0mx.
rewrite [row_mx 1%:M 0 *m block_mx _ _ _ _]mul_row_col mul1mx mul0mx addr0.
rewrite [row_mx ((-1 / M 0 0) *: dlsubmx M) _ *m _]mul_row_col mul1mx
 mul_mx_row add_row_mx mul_mx_scalar scalerA mulrC !mulNr -mulrA mulVr
 ?unitfE // !mul1r scaleNr scale1r addNr add_col_mx add0r addr0.
rewrite [drsubmx M - _]addrC.
rewrite scaleNr mulNmx.
set Mdr := - ((M 0 0)^-1 *: _ *m _) + _.
transitivity (\rank
  (col_mx (row_mx (col_mx (M 0 0)%:M 0) (col_mx (ursubmx M) Mdr))
                 (row_mx 0 vs))).
- by rewrite -!addsmxE addsmxC -block_mxEh.
transitivity (\rank (block_mx (M 0 0)%:M (ursubmx M) 0 (col_mx Mdr vs))).
- rewrite -!addsmxE -block_mxEh (adds_eqmx (eqmx_sym (addsmxE _ _))
   (eqmx_refl _)).
  rewrite -[X in row_mx X (col_mx _ _)]col_mx0 -block_mxEh -addsmxA.
  apply adds_eqmx; first by apply eqmx_refl.
  by apply addsmxE.
transitivity (1 + \rank (col_mx Mdr vs))%N.
- by rewrite rankaM' // -addsmxE addsmxC addsmxE.
congr (_ + _)%N.
rewrite -!addsmxE.
apply adds_eqmx; first by apply eqmx_refl.
apply (eqmx_trans (eqmx_sym (@addsmx0 _ _ 1 _ vs))).
rewrite addsmxC.
by apply addsmxE.
Qed.

Lemma ssr_rankP : forall n m (M: 'M[K]_(m,n)),
  ssr_rank M = \rank M.
Proof.
elim => [ | n hi].
- by move => m M; rewrite [M]thinmx0 mxrank0.
rewrite [n.+1]/(1 + n)%N => m M /=.
move: (@ssr_toolP _ 0%N _ 0 M).
move: (@ssr_tool_col0 _ 0%N _ 0 M).
case: ssr_tool => R b.
case: ifP => hb => [ _ | ].
- by rewrite row_mx0 adds0mx hi => ->.
rewrite -{3}[M]hsubmxK => ->.
rewrite rank0M' hi => ->.
by rewrite adds0mx.
Qed.

Fixpoint tool p (vs : seqmatrix K) {struct p}:
  seqmatrix K ->  (seqmatrix K * bool) :=
   match p return seqmatrix K -> (seqmatrix K * bool) with
   | p'.+1 => fun l =>
     let a := l 0%N 0%N in
     if a == 0 then
       tool p' (col_seqmx (ursubseqmx 1 1 l) vs) (dsubseqmx 1 l)
     else
       let v := scaleseqmx a^-1 (dlsubseqmx 1 1 l) in
       let R := subseqmx (drsubseqmx 1 1 l) (mulseqmx v (ursubseqmx 1 1 l)) in
       let v0 := mkseqmx 1 (size (rowseqmx l 0)).-1 (fun _ _ => 0) in
         (col_seqmx R (col_seqmx v0 vs), true)
   | _ => fun l => (vs, false)
end.

(*
Goal forall m n p (M : 'M[K]_(m,p)) (N : 'M[K]_(p,n)),
  mulseqmx (seqmx_of_mx M) (seqmx_of_mx N) = seqmx_of_mx (M *m N).
Proof.
move=> m ; case.
  move=> p M N.
rewrite [N]thinmx0 mulmx0.
rewrite /mulseqmx.


apply/seqmxP; split.


n p M N.
About mulseqmxE.
*)

Lemma toolE : forall p m n (vs : 'M_(m, n)) (M : 'M_(p, 1 + n)),
  let (R,b) := (ssr_tool vs M) in
  tool p (seqmx_of_mx vs) (seqmx_of_mx M) = (seqmx_of_mx R,b).
Proof.
elim=> // p IHs m n vs.
rewrite -add1n=> M.
rewrite /ssr_tool /= -seqmxE.
case:ifP=> //= H.
  move:(IHs _ _ (col_mx (ursubmx M) vs) (dsubmx M)).
  rewrite -/(ssr_tool _ _); case:(ssr_tool _ _)=> R b H1.
  by rewrite ursubseqmxE col_seqmxE dsubseqmxE H1 cast_seqmx.
set mk0seqmx := mkseqmx 1 _ _.
have -> : mk0seqmx = seqmx_of_mx (0 : 'rV_n).
  apply/seqmxP; split=> [|i Hi|i j].
    + by rewrite size_mkseq.
    + by rewrite size_row_mkseqmx // (@size_row_seqmx _ _ _ M 0).
    + by rewrite mkseqmxE ? mxE // (@size_row_seqmx _ _ _ M 0).
rewrite cast_seqmx -!col_seqmxE subseqmxE -drsubseqmxE -mulseqmxE -scaleseqmxE.
by rewrite -ursubseqmxE -dlsubseqmxE.
Qed.

Fixpoint rank (m n:nat) {struct n} : seqmatrix K -> nat :=
  match n return seqmatrix K -> nat with
   |  q.+1 => fun M => let:(R,b) := @tool m [::] M in
     (b + rank m q R)%N
   | _ => fun _ => 0%N
end.

Lemma rankE : forall m n (M : 'M_(m, n)),
  rank m n (seqmx_of_mx M) = ssr_rank M.
Proof.
move=> m; elim=> // n IHn M.
rewrite /rank /ssr_rank; move:(@toolE m 0 n 0 M); case:(ssr_tool _ _).
by rewrite addn0=> R b; rewrite seqmx0n=> ->; rewrite -/rank IHn.
Qed.

End FieldRank.

Require Import prime.

(* to use the F2 implementation of SSR, we first need to prove
   that 2 is a prime number *)
Lemma p2 : prime 2%N.
Proof.
apply/primeP.
split => // d.
case : d => [ | d].
- by rewrite dvd0n.
move/dvdn_leq.
case: d => [ | d].
- by rewrite eq_refl.
case: d => [ | d] hd.
- by rewrite eq_refl orbT.
assert (0 < 2) by apply ltn0Sn.
have : d.+2 < 2 by apply hd.
change (d.+2) with (1 + (1 + d)).
change 2 with (1 + (1 + 0)).
by rewrite 2!ltn_add2l ltn0.
Qed.

Definition F2 := Fp_fieldType 2.

Notation "n %:F2" := (n%R : 'F_2) (at level 2, left associativity, format "n %:F2").

(*
Definition M := [::
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2]
].


Eval vm_compute in (size M).

Eval vm_compute in (size (head [::] M)).

Time Eval vm_compute in (rank 9 348 M).

*)