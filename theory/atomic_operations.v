
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import ssralg fintype perm choice.
From mathcomp Require Import matrix  bigop zmodp mxalgebra poly mxpoly.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

Section atomic_operations.
Variable R: comRingType.

(* describe simple line / column combination operators *)

(* Operation to multiply Lk by a the scalar a *)
Definition line_scale n m k (a: R) (M: 'M[R]_(n,m)) :=
  \matrix_(i < n) ((if i == k then a else 1) *: row i M).

Lemma line_scale_row_eq n m k a (M: 'M[R]_(n,m)):
  row k (line_scale k a M) = a *: row k M.
Proof.
by apply/rowP => i; rewrite !mxE eqxx.
Qed.

Lemma line_scale_row_neq n m k l a (M: 'M[R]_(n,m)): k != l ->
  row l (line_scale k a M) = row l M.
Proof.
move/negbTE => hkl.
by apply/rowP => i; rewrite !mxE eq_sym hkl mul1r.
Qed.


(* several application of the line_scale operation *)
Lemma lines_scale_row m n a (M: 'M[R]_(m,n)):
  forall s, uniq s ->
  (forall i, i \in s ->
    row i (foldl (fun N i => line_scale i a N) M s) = a *: row i M) /\
  (forall i, i \notin s ->
    row i (foldl (fun N i => line_scale i a N) M s) = row i M).
Proof.
move => s.
elim : s n M => [ | hd tl hi] //= n M /andP [h1 h2].
split => i.
- rewrite in_cons => /orP [] hin.
  + rewrite (eqP hin) {i hin}.
    case: (hi _ (line_scale hd a M) h2) => _ hr.
    by rewrite hr // line_scale_row_eq.
  case: (hi _ (line_scale hd a M) h2) => hl _.
  rewrite hl // line_scale_row_neq //.
  apply/negP => /eqP heq.
  by move: h1; rewrite heq hin.
rewrite in_cons negb_or => /andP [hl hr].
case: (hi _ (line_scale hd a M)  h2) => _ hR.
by rewrite hR // line_scale_row_neq // eq_sym.
Qed.

(*
  alternative definition of the same operation by matrix multiplication
  this definition is easier to prove determinant property of the operator
*)
Definition line_scale_mx n m k (a: R) (M: 'M[R]_(n,m)) :=
  diag_mx (\row_(i < n) (if i == k then a else 1)) *m M.

Lemma line_scale_eq : forall n m k a (M: 'M[R]_(n,m)),
  line_scale k a M = line_scale_mx k a M.
Proof.
move => n m k a M; apply/matrixP => i j; rewrite !mxE.
rewrite (bigD1 i) //= big1 /=; first by rewrite !mxE addr0 eqxx.
by move => x /negbTE hx; rewrite !mxE [i == x]eq_sym hx mulr0n mul0r.
Qed.

(* line_scale_mx scales the determinant by a *)
Lemma det_line_scale_mx : forall n k a (M: 'M[R]_n),
  \det (line_scale_mx k a M) = a * \det M.
Proof.
rewrite /line_scale_mx => n k a M.
rewrite det_mulmx det_diag (bigD1 k) //= big1 /=;
  first by rewrite !mxE mulr1 eqxx /=.
by move => i /negbTE h; rewrite !mxE h.
Qed.

(* line_scale scales the determinant by a *)
Lemma det_line_scale : forall n k a (M: 'M[R]_n),
  \det (line_scale k a M) = a * \det M.
Proof.
move => n k a M.
by rewrite line_scale_eq det_line_scale_mx.
Qed.

Lemma det_lines_scale m a (M: 'M[R]_m) s:
  \det (foldl (fun N i => line_scale i a N) M s) = a ^+ (size s) * \det M.
Proof.
elim : s M => [ | hd tl hi] M //=.
- by rewrite expr0 mul1r.
by rewrite hi det_line_scale mulrA exprSr.
Qed.


(* Operation to change Lk by Lk + a Ll *)
Definition line_comb n m k l (a: R) (M: 'M[R]_(n,m)) :=
  \matrix_(i < n) if i == k then row k M + a*: row l M else row i M.


Lemma line_comb_row_eq n m k l a (M: 'M[R]_(n,m)):
  row k (line_comb k l a M) = row k M + a *: row l M.
Proof.
by apply/rowP => i; rewrite !mxE eqxx !mxE.
Qed.

Lemma line_comb_row_neq n m k k' l a (M: 'M[R]_(n,m)): k != k' ->
  row k' (line_comb k l a M) = row k' M.
Proof.
move/negbTE => hkk'.
by apply/rowP => i; rewrite !mxE eq_sym hkk' !mxE.
Qed.

(* several application of the line_comb operation *)
Lemma lines_comb_row m n a l (M: 'M[R]_(m,n)):
  forall s, uniq s -> l \notin s ->
  (forall i, i \in s ->
    row i (foldl (fun N i => line_comb i l a N) M s) =
    row i M + a *: row l M) /\
  (forall i, i \notin s ->
    row i (foldl (fun N i => line_comb i l a N) M s) = row i M).
Proof.
move => s.
elim : s M => [ | hd tl hi] //= M /andP [h1 h2].
rewrite in_cons negb_or => /andP [hl1 hl2].
split => i.
- rewrite in_cons => /orP [] hin.
  + rewrite (eqP hin) {i hin}.
    case: (hi (line_comb hd l a M) h2 hl2) => _ hr.
    by rewrite hr // line_comb_row_eq.
  case: (hi (line_comb hd l a M) h2 hl2) => hl _.
  rewrite hl //  !line_comb_row_neq //.
  + by rewrite eq_sym.
  apply/negP => /eqP heq.
  by move: h1; rewrite heq hin.
rewrite in_cons negb_or => /andP [hl hr].
case: (hi (line_comb hd l a M)  h2 hl2) => _ hR.
by rewrite hR // !line_comb_row_neq // eq_sym.
Qed.


Lemma lines_comb_row_dep m n (a: 'I_m -> R) l (M: 'M[R]_(m,n)):
  forall s, uniq s -> l \notin s ->
  (forall i, i \in s ->
    row i (foldl (fun N i => line_comb i l (a i) N) M s) =
    row i M + (a i) *: row l M) /\
  (forall i, i \notin s ->
    row i (foldl (fun N i => line_comb i l (a i) N) M s) = row i M).
Proof.
move => s.
elim : s M => [ | hd tl hi] //= M /andP [h1 h2].
rewrite in_cons negb_or => /andP [hl1 hl2].
split => i.
- rewrite in_cons => /orP [] hin.
  + rewrite (eqP hin) {i hin}.
    case: (hi (line_comb hd l (a hd) M) h2 hl2) => _ hr.
    by rewrite hr // line_comb_row_eq.
  case: (hi (line_comb hd l (a hd) M) h2 hl2) => hl _.
  rewrite hl //  !line_comb_row_neq //.
  + by rewrite eq_sym.
  apply/negP => /eqP heq.
  by move: h1; rewrite heq hin.
rewrite in_cons negb_or => /andP [hl hr].
case: (hi (line_comb hd l (a hd) M)  h2 hl2) => _ hR.
by rewrite hR // !line_comb_row_neq // eq_sym.
Qed.

(* if k != l, line_comb doesn't change the det *)
Lemma det_line_comb : forall n k l a (M: 'M[R]_n),
  k != l -> \det (line_comb k l a M) = \det M.
Proof.
move => n k l a M hkl.
have h : row k (line_comb k l a M) = 1 *: row k M +
  a *: row k (\matrix_(i < n) if i == k then row l M else row i M).
- rewrite /line_comb scale1r.
  by apply/rowP => i; rewrite !mxE eqxx !mxE.
rewrite (determinant_multilinear h).
- rewrite mul1r [X in a * X](determinant_alternate hkl).
  + by rewrite mulr0 addr0.
  move => x; rewrite !mxE eqxx eq_sym.
  move: hkl.
  by case hlk : (k == l).
- rewrite /line_comb; apply/matrixP => i j; rewrite !mxE.
  case heq: (lift k i == k).
  + move/negP : (neq_lift k i).
    by rewrite (eqP heq) eqxx.
  by rewrite !mxE.
- rewrite /line_comb; apply/matrixP => i j; rewrite !mxE.
  case heq: (lift k i == k).
  + move/negP : (neq_lift k i).
    by rewrite (eqP heq) eqxx.
  by rewrite !mxE.
Qed.

Lemma det_lines_comb m a l (M: 'M[R]_m) s:
  l \notin s ->
  \det (foldl (fun N i => line_comb i l a N) M s) = \det M.
Proof.
elim : s M => [ | hd tl hi] M //=.
rewrite in_cons negb_or => /andP [hl1 hl2].
by rewrite hi // det_line_comb // eq_sym.
Qed.

Lemma det_lines_comb_dep m (a: 'I_m -> R) l (M: 'M[R]_m) s:
  l \notin s ->
  \det (foldl (fun N i => line_comb i l (a i) N) M s) = \det M.
Proof.
elim : s M => [ | hd tl hi] M //=.
rewrite in_cons negb_or => /andP [hl1 hl2].
by rewrite hi // det_line_comb // eq_sym.
Qed.


(* if k == l, line_comb == line_scale *)
Lemma det_line_comb_eq : forall n k l a (M: 'M[R]_n),
  k == l -> \det (line_comb k l a M) = (1 + a) * \det M.
Proof.
move => n k l a M /eqP ->; clear k.
have h : row l (line_comb l l a M) = 1 *: row l M + a *: row l M.
- rewrite /line_scale.
  by apply/rowP => i; rewrite !mxE eqxx !mxE mul1r.
rewrite (determinant_multilinear h) ?mulrDl => //.
  rewrite /line_scale; apply/matrixP => i j; rewrite !mxE.
  case heq: (lift l i == l).
  + move/negP : (neq_lift l i).
    by rewrite (eqP heq) eqxx.
  by rewrite !mxE.
rewrite /line_scale; apply/matrixP => i j; rewrite !mxE.
case heq: (lift l i == l).
- move/negP : (neq_lift l i).
  by rewrite (eqP heq) eqxx.
by rewrite !mxE.
Qed.

End atomic_operations.