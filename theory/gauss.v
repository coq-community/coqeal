(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp Require Import mxalgebra perm zmodp matrix ssrint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Gaussian.

Import GRing.Theory.

Local Open Scope ring_scope.

Variable F : fieldType.

Definition find_pivot m n (A : 'M[F]_(m,n.+1)) : option 'I_m :=
  [pick k | A k 0 != 0].

Fixpoint cormen_lup {m n} :=
  match m, n return 'M_(m.+1,n.+1) -> 'S_m.+1 * 'M_(m.+1,m.+1) * 'M_(m.+1,n.+1) with
  | p.+1, _.+1 => fun (A : 'M_(1 + (1 + p), 1 + _)) =>
    let k := odflt 0 (find_pivot A) in
    let A1 : 'M_(1 + _, 1 + _) := xrow 0 k A in
    let P1 : 'S_(1 + (1 + p)) := tperm 0 k in
    let Schur := ((fun_of_matrix A k 0)^-1 *: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur) in
    let P := (lift0_perm P2 * P1)%g in
    let pA1 := row_perm P2 (dlsubmx A1) in
    let L := block_mx 1%:M (const_mx 0) ((fun_of_matrix A k 0)^-1 *: pA1) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) (const_mx 0) U2 in
    (P, L, U)
  | _, _ => fun A => (1%g, 1%:M, A)
  end.

Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lup A in matrix.row_perm P A = L * U.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite row_perm1 mul1r.
set k := odflt _ _; set A1 : 'M_(1 + _) := matrix.xrow _ _ _.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P' L' U']] /= IHn.
(* glueing code *)
rewrite row_permM !row_permE.
rewrite -lift0_mx_perm.
rewrite /lift0_mx.
(****************)
rewrite -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
rewrite row_permE.
rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulrDr {A'}subrK.
congr (block_mx _ _ (_ *m _) _).
rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k /find_pivot.
case: pickP => /= [k nzAk0 | no_k]; first by rewrite mulVf ?mulmx1.
rewrite (_ : matrix.dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
by rewrite !mxE lshift0 (elimNf eqP (no_k _)).
Qed.

Lemma cormen_lup_detL n (A : 'M_n.+1) : \det (cormen_lup A).1.2 = 1.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite det1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= detL.
by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

Lemma cormen_lup_lower n (A : 'M_n.+1) (i j : 'I_n.+1) :
  i <= j -> (cormen_lup A).1.2 i j = (i == j)%:R.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1 [j]ord1 mxE.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Ll.
rewrite !mxE split1; case: unliftP => [i'|] -> /=; rewrite !mxE split1.
  by case: unliftP => [j'|] -> //; exact: Ll.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma cormen_lup_upper n A (i j : 'I_n.+1) :
  j < i -> (cormen_lup A).2 i j = 0 :> F.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Uu.
rewrite !mxE split1; case: unliftP => [i'|] -> //=; rewrite !mxE split1.
by case: unliftP => [j'|] ->; [exact: Uu | rewrite /= mxE].
Qed.

End Gaussian.
