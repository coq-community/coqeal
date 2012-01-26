(* This file is part of CoqEAL, the Coq Effective Algebra Library *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import ssralg fintype perm matrix bigop zmodp mxalgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This file contains definitions and lemmas that are generic enough that *)
(* we could try to integrate them in Math Components' library.            *)
(* Definitions and theories are gathered according to the file of the     *)
(* library to which they could be moved.                                  *)

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
by case=> // t2 s2 H ; rewrite /= IHs // ; move:H ; rewrite !leq_minr.
Qed.

Fixpoint foldl2 (f : T3 -> T1 -> T2 -> T3) z (s : seq T1) (t : seq T2) {struct s} :=
  if s is x :: s' then
    if t is y :: t' then foldl2 f (f z x y) s' t' else z
  else z.

End Seq.

(********************* matrix.v *********************)
Section Matrix.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable R : ringType.
Variable n m : nat.

End Matrix.