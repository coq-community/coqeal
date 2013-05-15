(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements seqmatrix.

Section Strassen_generic.

Local Open Scope ring_scope.

(** K is the size threshold below which we switch back to naive
multiplication *)
Let K := 32%positive.

Local Coercion nat_of_pos : positive >-> nat.

Lemma addpp p : xO p = (p + p)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addSpp p : xI p = (p + p).+1%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addp1 p : xI p = (xO p + 1)%N :> nat.
Proof. by rewrite addn1. Qed.

Lemma addpp1 p : xI p = (p + p + 1)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn addn1. Qed.

Lemma lt0p : forall p : positive, 0 < p.
Proof.
by elim=> // p IHp /=; rewrite NatTrec.doubleE -addnn; exact:ltn_addl.
Qed.

Import Refinements.Op.

Variable mxA : nat -> nat -> Type.
Variables (addmx submx : forall (m n : nat), mxA m n -> mxA m n -> mxA m n).
Variable mulmx : forall (m n p : nat), mxA m n -> mxA n p -> mxA m p.
Variable ulsubmx : forall (m1 m2 n1 n2 : nat), mxA (m1 + m2) (n1 + n2) -> mxA m1 n1.
Variable ursubmx : forall (m1 m2 n1 n2 : nat), mxA (m1 + m2) (n1 + n2) -> mxA m1 n2.
Variable dlsubmx : forall (m1 m2 n1 n2 : nat), mxA (m1 + m2) (n1 + n2) -> mxA m2 n1.
Variable drsubmx : forall (m1 m2 n1 n2 : nat), mxA (m1 + m2) (n1 + n2) -> mxA m2 n2.
Variable block_mx : forall (m1 m2 n1 n2 : nat),
  mxA m1 n1 -> mxA m1 n2 -> mxA m2 n1 -> mxA m2 n2 -> mxA (m1 + m2) (n1 + n2).
Variable castmx : forall (m n m' n' : nat),
  (m = m') * (n = n') -> mxA m n -> mxA m' n'.

Arguments ulsubmx {m1 m2 n1 n2} _.
Arguments ursubmx {m1 m2 n1 n2} _.
Arguments dlsubmx {m1 m2 n1 n2} _.
Arguments drsubmx {m1 m2 n1 n2} _.
Arguments addmx {m n} _ _.
Arguments submx {m n} _ _.
Arguments block_mx {m1 m2 n1 n2} _ _ _ _.
Arguments mulmx {m n p} _ _.
Arguments castmx {m n m' n'} _ _.


Definition Strassen_step {p : positive} (A B : mxA (p + p) (p + p)) f :
  mxA (p + p) (p + p) :=
  let A11 := ulsubmx A in
  let A12 := ursubmx A in
  let A21 := dlsubmx A in
  let A22 := drsubmx A in
  let B11 := ulsubmx B in
  let B12 := ursubmx B in
  let B21 := dlsubmx B in
  let B22 := drsubmx B in
  let X := submx A11 A21 in
  let Y := submx B22 B12 in
  let C21 := f X Y in
  let X := addmx A21 A22 in
  let Y := submx B12 B11 in
  let C22 := f X Y in
  let X := submx X A11 in
  let Y := submx B22 Y in
  let C12 := f X Y in
  let X := submx A12 X in
  let C11 := f X B22 in
  let X := f A11 B11 in
  let C12 := addmx X C12 in
  let C21 := addmx C12 C21 in
  let C12 := addmx C12 C22 in
  let C22 := addmx C21 C22 in
  let C12 := addmx C12 C11 in
  let Y := submx Y B21 in
  let C11 := f A22 Y in
  let C21 := submx C21 C11 in
  let C11 := f A12 B21 in
  let C11 := addmx X C11 in
  block_mx C11 C12 C21 C22.

Fixpoint Strassen {n : positive} {struct n} :=
  match n return let M := mxA n n in M -> M -> M with
  | xH => fun M N => mulmx M N
  | xO p => fun A B =>
    if p <= K then mulmx A B else
    let A := castmx (addpp p,addpp p) A in
    let B := castmx (addpp p,addpp p) B in
    castmx (esym (addpp p),esym (addpp p)) (Strassen_step A B Strassen)
  | xI p => fun M N =>
    if p <= K then mulmx M N else
    let M := castmx (addpp1 p, addpp1 p) M in
    let N := castmx (addpp1 p, addpp1 p) N in
    let M11 := ulsubmx M in
    let M12 := ursubmx M in
    let M21 := dlsubmx M in
    let M22 := drsubmx M in
    let N11 := ulsubmx N in
    let N12 := ursubmx N in
    let N21 := dlsubmx N in
    let N22 := drsubmx N in
    let C := addmx (Strassen_step M11 N11 Strassen) (mulmx M12 N21) in
    let R12 := addmx (mulmx M11 N12) (mulmx M12 N22) in
    let R21 := addmx (mulmx M21 N11) (mulmx M22 N21) in
    let R22 := addmx (mulmx M21 N12) (mulmx M22 N22) in
    castmx (esym (addpp1 p), esym (addpp1 p)) (block_mx C R12 R21 R22)
end.

End Strassen_generic.

Section Strassen_abstract.

Variable R : ringType.

Definition Strassen_abstract {p} := @Strassen (matrix R) (@addmx R) (fun m n x => @addmx R m n (oppmx x)) (@mulmx R) (@ulsubmx R) (@ursubmx R) (@dlsubmx R) (@drsubmx R) (@block_mx R) (@castmx R) p.

End Strassen_abstract.

Section Strassen_seqmx.

Import Refinements.Op.

Variable A : Type.
Context `{add A, sub A, mul A, zero A}.

Definition Strassen_seqmx := @Strassen (fun _ _ => seqmatrix A) (fun _ _ => @addseqmx A _) (fun _ _ => @subseqmx A _) (fun _ => @mulseqmx A _ _ _) (fun m1 _ n1 _ => @ulsubseqmx A m1 n1) (fun m1 _ n1 _ => @ursubseqmx A m1 n1) (fun m1 _ n1 _ => @dlsubseqmx A m1 n1) (fun m1 _ n1 _ => @drsubseqmx A m1 n1) (fun _ _ _ _ => @block_seqmx A) (fun _ _ _ _ _ x => x).

(*
Eval cbv delta[Strassen_seqmx Strassen] beta zeta in Strassen_seqmx.
*)

End Strassen_seqmx.