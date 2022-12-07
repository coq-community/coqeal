(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import zmodp path choice fintype tuple finset ssralg.
From mathcomp Require Import bigop poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.

Section karatsuba.

Variable R : ringType.
Definition split_poly n (p : {poly R}) := (rdivp p 'X^n, rmodp p 'X^n).
Definition shift_poly n : {poly R} -> {poly R} := *%R^~ 'X^n.
Definition normalize (p : {poly R}) := p.

Fixpoint karatsuba_rec (n : nat) (p q : {poly R}) :=
  if n is n'.+1 then
    let np := normalize p in  let nq := normalize q in
    let sp := size p in let sq := size q in
    if (sp <= 2) || (sq <= 2) then p * q else
      let m       := minn sp./2 sq./2 in
      let (p1,p2) := split_poly m p in
      let (q1,q2) := split_poly m q in
      let p1q1    := karatsuba_rec n' p1 q1 in
      let p2q2    := karatsuba_rec n' p2 q2 in
      let p12     := p1 + p2 in
      let q12     := q1 + q2 in
      let p12q12  := karatsuba_rec n' p12 q12 in
      shift_poly (2 * m)%N p1q1 +
       shift_poly m (p12q12 - p1q1 - p2q2) +
       p2q2
  else p * q.

Definition karatsuba (p q : {poly R}) :=
  karatsuba_rec (maxn (size p) (size q)) p q.

Lemma karatsuba_recE n (p q : {poly R}) : karatsuba_rec n p q = p * q.
Proof.
elim: n=> //= n ih in p q *; case: ifP=> // _; set m := minn _ _.
rewrite [p in RHS](rdivp_eq (monicXn _ m)) [q in RHS](rdivp_eq (monicXn _ m)).
set dp := rdivp p _; set dq := rdivp q _; set rp := rmodp p _; set rq := rmodp q _.
rewrite /shift_poly /split_poly !ih !(mulrDr, mulrDl, mulNr) mulnC exprM.
rewrite -[_ - _ - _]addrA [_ + _ + (- _ - _)]addrACA [_ + _ - _]addrAC.
by rewrite subrr add0r addrK !(commr_polyXn, mulrA, addrA).
Qed.

Lemma karatsubaE (p q : {poly R}) : karatsuba p q = p * q.
Proof. exact: karatsuba_recE. Qed.

End karatsuba.
