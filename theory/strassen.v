(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ZArith Ncring Ncring_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp Require Import perm zmodp matrix.

Require Import ssralg_ring_tac.

(** This file describes a formally verified implementation of Strassen's
algorithm (Winograd's variant). *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Strassen.
Variable (R : ringType) (K : positive).

Local Coercion nat_of_pos : positive >-> nat.

Lemma addpp p : xO p = (p + p)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addSpp p : xI p = (p + p).+1%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addp1 p : xI p = (xO p + 1)%N :> nat.
Proof. by rewrite addn1. Qed.

Lemma add1pp p : xI p = (1 + (p + p))%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma lt0p : forall p : positive, 0 < p.
Proof.
by elim=> // p IHp /=; rewrite NatTrec.doubleE -addnn; exact:ltn_addl.
Qed.

Local Open Scope ring_scope.


Definition Strassen_step {p : positive} (A B : 'M[R]_(p + p, p + p))
  (f : 'M[R]_(p, p) -> 'M_(p, p) -> 'M[R]_(p, p)) : 'M_(p + p, p + p) :=
  let A11 := ulsubmx A in
  let A12 := ursubmx A in
  let A21 := dlsubmx A in
  let A22 := drsubmx A in
  let B11 := ulsubmx B in
  let B12 := ursubmx B in
  let B21 := dlsubmx B in
  let B22 := drsubmx B in
  let X := A11 - A21 in
  let Y := B22 - B12 in
  let C21 := f X Y in
  let X := A21 + A22 in
  let Y := B12 - B11 in
  let C22 := f X Y in
  let X := X - A11 in
  let Y := B22 - Y in
  let C12 := f X Y in
  let X := A12 - X in
  let C11 := f X B22 in
  let X := f A11 B11 in
  let C12 := X + C12 in
  let C21 := C12 + C21 in
  let C12 := C12 + C22 in
  let C22 := C21 + C22 in
  let C12 := C12 + C11 in
  let Y := Y - B21 in
  let C11 := f A22 Y in
  let C21 := C21 - C11 in
  let C11 := f A12 B21 in
  let C11 := X + C11 in
  block_mx C11 C12 C21 C22.

Definition Strassen_xO {p : positive} Strassen_p :=
  fun A B =>
    if p <= K then A *m B else
    let A := castmx (addpp p,addpp p) A in
    let B := castmx (addpp p,addpp p) B in
    castmx (esym (addpp p), esym (addpp p)) (Strassen_step A B Strassen_p).
  
Definition Strassen_xI {p : positive} Strassen_p :=
   fun M N =>
    if p <= K then M *m N else
    let M := castmx (add1pp p, add1pp p) M in
    let N := castmx (add1pp p, add1pp p) N in
    let M11 := ulsubmx M in
    let M12 := ursubmx M in
    let M21 := dlsubmx M in
    let M22 := drsubmx M in
    let N11 := ulsubmx N in
    let N12 := ursubmx N in
    let N21 := dlsubmx N in
    let N22 := drsubmx N in
    let R11 := (M11 *m N11) + (M12 *m N21) in
    let R12 := (M11 *m N12) + (M12 *m N22) in
    let R21 := (M21 *m N11) + (M22 *m N21) in
    let R22 := (M21 *m N12) + (Strassen_step M22 N22 Strassen_p) in
    castmx (esym (add1pp p), esym (add1pp p)) (block_mx R11 R12 R21 R22).

Definition Strassen := 
  (positive_rect (fun p => ('M_(p, p) -> 'M_(p, p) -> 'M_(p, p)))
                 (@Strassen_xI) (@Strassen_xO) (fun M N => M *m N)).


Lemma Strassen_stepP (p : positive) (A B : 'M[R]_(p + p)) f :
  f =2 mulmx -> Strassen_step A B f = A *m B.
Proof.
move=> Hf; rewrite -{2}[A]submxK -{2}[B]submxK mulmx_block /Strassen_step !Hf.
rewrite /GRing.add /= /GRing.opp /=.
by congr block_mx; non_commutative_ring.
Qed.

Lemma mulmx_cast {R' : ringType} {m n p m' n' p'} {M:'M[R']_(m,p)} {N:'M_(p,n)}
  {eqm : m = m'} (eqp : p = p') {eqn : n = n'} :
  matrix.castmx (eqm,eqn) (M *m N) = matrix.castmx (eqm,eqp) M *m matrix.castmx (eqp,eqn) N.
Proof. by case eqm ; case eqn ; case eqp. Qed.

Lemma StrassenP p : mulmx =2 (Strassen (p := p)).
Proof.
elim: p => // [p IHp|p IHp] M N.
  rewrite /= /Strassen_xI; case:ifP=> // _.
  by rewrite Strassen_stepP // -mulmx_block !submxK -mulmx_cast castmxK.
rewrite /= /Strassen_xO; case:ifP=> // _.
by rewrite Strassen_stepP // -mulmx_cast castmxK.
Qed.

End Strassen.
