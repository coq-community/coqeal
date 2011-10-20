Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import ssralg fintype perm.
Require Import matrix  bigop zmodp mxalgebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section MatrixFacts.
Variable R : fieldType.

Local Open Scope ring_scope.


Lemma lift0_unitmx : forall (n:nat) (M: 'M[R]_n), M \in unitmx ->
  lift0_mx M \in unitmx.
Proof.
by move => n M; rewrite !unitmxE det_ublock det1 mul1r.
Qed.


Lemma scale_add_distr: forall (n m:nat) (a b: R) (M: 'M[R]_(n,m)),
  a *: M + b *: M = (a + b) *: M.
Proof.
move => n m a b M.
apply/matrixP => i j; rewrite !mxE /=.
by rewrite mulr_addl.
Qed.

Lemma dsub_mulmx : forall (n m p q:nat) (M:'M[R]_(n+m,p)) (N :'M[R]_(p,q)),
  dsubmx (M *m N) = dsubmx M *m N.
Proof.
move => n m p q M N.
by rewrite -{1}[M]vsubmxK mul_col_mx col_mxKd.
Qed.

(* :=: is an equality in mxalgebra that say both matrices behave
   the same according to rank

  Here, it says that the rank of 0M is the same as M
*)
Lemma eqmxM0M : forall (n m:nat) (M: 'M[R]_(n,m)),
 ((@col_mx R 1 n m 0 M) :=: M)%MS.
Proof.
move => n m M.
apply (eqmx_trans (eqmx_sym (@addsmxE R 1 n m 0 M))).
rewrite addsmxC.
by apply addsmx0.
Qed.

Lemma trmx_eq0 : forall (n m:nat) (M: 'M[R]_(n,m)),
 (M == 0) = (M^T == 0).
Proof.
move => n m M.
apply/eqP/eqP.
- by move => ->; rewrite trmx0.
by move => h; rewrite -[M]trmxK h trmx0.
Qed.

Lemma trmx_neq0 : forall (n m:nat) (M: 'M[R]_(n,m)),
 (M != 0) = (M^T != 0).
Proof.
move => n m M.
apply/negP/negP.
- move => h1 h2; apply: h1.
  by rewrite trmx_eq0.
move => h1 h2; apply: h1.
by rewrite -trmx_eq0.
Qed.

(* row_full : rank and width of the matrix are equal *)
Lemma nzscalar_row_full : forall (n:nat) (a: R), a != 0 ->
  row_full (a%:M : 'M[R]_n).
Proof.
move => n a ha.
by rewrite -col_leq_rank -scalemx1 mxrank_scale_nz ?mxrank1.
Qed.


Lemma scalar_add: forall (n:nat) (a b: R),
 (a + b)%:M = a%:M + b%:M :> 'M_n.
Proof.
move => n a b.
by apply/matrixP => i j; rewrite !mxE mulrn_addl.
Qed.

Lemma scalar0: forall n, 0%:M = 0 :> 'M[R]_n.
Proof.
move => n; apply/matrixP => i j; rewrite !mxE.
by rewrite mul0rn.
Qed.


Lemma col_matrixP : forall (n m:nat) (A B:'M[R]_(n, m)),
  (forall i, col i A = col i B) <-> A = B.
Proof.
move => n m A B.
have := (row_matrixP A^T B^T).
case => h1 h2.
split => h.
- rewrite -[A]trmxK -[B]trmxK h1 => // i.
  by rewrite -!tr_col (h i).
by move => i; rewrite h.
Qed.



End MatrixFacts.
