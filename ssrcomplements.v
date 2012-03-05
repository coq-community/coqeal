(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import ssralg fintype perm matrix bigop zmodp mxalgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** This file contains definitions and lemmas that are generic enough that
we could try to integrate them in Math Components' library.
Definitions and theories are gathered according to the file of the
library which they could be moved to. *)

(********************* seq.v *********************)
Section Seq.

Variables (T1 T2 T3 : Type) (f : T1 -> T2 -> T3).

Fixpoint zipwith (s1 : seq T1) (s2 : seq T2) :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then f x1 x2 :: zipwith s1' s2' else [::]
  else [::].

Lemma size_zipwith s1 s2 :
  size (zipwith s1 s2) = minn (size s1) (size s2).
Proof.
elim:s1 s2=>[s2|t1 s1 IHs] ; first by rewrite min0n.
by case=>[|t2 s2] //= ; rewrite IHs /minn /leq subSS ; case:ifP.
Qed.

Lemma nth_zipwith x1 x2 x3 n s1 s2 :
  n < minn (size s1) (size s2) ->
  nth x3 (zipwith s1 s2) n = f (nth x1 s1 n) (nth x2 s2 n).
Proof.
elim:s1 n s2=> [n s2|t1 s1 IHs]; first by rewrite min0n ltn0.
case=>[|n]; first by case.
by case=> // t2 s2 H ; rewrite /= IHs // ; move:H ; rewrite !leq_min.
Qed.

Fixpoint foldl2 (f : T3 -> T1 -> T2 -> T3) z (s : seq T1) (t : seq T2) {struct s} :=
  if s is x :: s' then
    if t is y :: t' then foldl2 f (f z x y) s' t' else z
  else z.

End Seq.

Section BigOp.

Lemma sumn_big s : sumn s = (\sum_(i <- s) i)%N.
Proof.
elim: s=> /= [|a l ->]; first by rewrite big_nil.
by rewrite big_cons.
Qed.

End BigOp.

(********************* matrix.v *********************)
Section Matrix.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable R : ringType.

Lemma scalar_mx0 (n : nat) : 0%:M = 0 :> 'M[R]_n.
Proof. by rewrite -scalemx1 scale0r. Qed.

(* Lemmas about column operations *)
Lemma colE (m n : nat) i (A : 'M[R]_(m, n)) : col i A = A *m delta_mx i 0.
Proof.
apply/colP=> j; rewrite !mxE (bigD1 i) //= mxE !eqxx mulr1.
by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mulr0.
Qed.

Lemma col_matrixP (m n : nat) :
  forall (A B : 'M[R]_(m,n)), (forall i, col i A = col i B) <-> A = B.
Proof.
split=> [eqAB | -> //]; apply/matrixP=> i j.
by move/colP/(_ i): (eqAB j); rewrite !mxE.
Qed.

Lemma col_mul m n p (i : 'I_p) (A : 'M[R]_(m,n)) (B : 'M[R]_(n, p)) :
  col i (A *m B) = A *m col i B.
Proof. by rewrite !colE mulmxA. Qed.

(* Lemma about mxvec *)
Lemma mxvec0 m n : mxvec (0 : 'M[R]_(m,n)) = 0 :> 'rV[R]_(m * n).
Proof. by apply/eqP; rewrite mxvec_eq0. Qed.

Lemma tr_mxvec m n (M : 'M[R]_(m,n)) i j :
  (mxvec M) 0 (mxvec_index i j) = (mxvec M^T) 0 (mxvec_index j i).
Proof. by rewrite !mxvecE mxE. Qed.

Lemma scale_mxvec m n x (M : 'M[R]_(m,n)) : mxvec (x *: M) = x *: mxvec M.
Proof.
apply/rowP => i; rewrite mxE.
case/mxvec_indexP: i => i j.
by rewrite !mxvecE !mxE.
Qed.

Definition pairxx (T : Type) (x : T) := pair x x.

Lemma row_flat_mx (M : 'M_(m,0)) (N : 'M[R]_(m,n)) :
  row_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case: (splitP j) => [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

Lemma col_flat_mx (M : 'M[R]_(0, m)) (N : 'M_(n,m)) :
  col_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite !mxE; case (splitP i)=> [| k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

End Matrix.