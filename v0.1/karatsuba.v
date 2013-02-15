(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg poly.
Require Import bigop cssralg cseqpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Import GRing.Theory.
Local Open Scope ring_scope.

Section karatsuba.

Variable R : comRingType.
Variable CR : cringType R.

Implicit Types p q : {poly R}.

(* Splitting polynomials *)
Definition splitp n p := (Poly (drop n p), Poly (take n p)).

Lemma splitP n p : p = (splitp n p).1 * 'X^n + (splitp n p).2.
Proof.
apply/polyP=> i; rewrite coefD coefMXn !coef_Poly nth_drop addnC.
have [i_lt_n|n_leq_i] := ltnP; first by rewrite add0r nth_take.
rewrite subnK ?[(take _ _)`_i]nth_default ?addr0 // size_take.
by have [//|sp_leq_n] := ltnP; apply/(leq_trans sp_leq_n).
Qed.

(* Karatsuba multiplication *)
Fixpoint karatsuba_rec (n : nat) p q := match n with
  | 0%N   => p * q
  | n'.+1 => 
      let sp := size p in let sq := size q in 
      if (sp <= 2) || (sq <= 2) then p * q else
        let m       := minn sp./2 sq./2 in
        let (p1,p2) := splitp m p in
        let (q1,q2) := splitp m q in
        let p1q1    := karatsuba_rec n' p1 q1 in
        let p2q2    := karatsuba_rec n' p2 q2 in
        let p12     := p1 + p2 in
        let q12     := q1 + q2 in
        let p12q12  := karatsuba_rec n' p12 q12 in
        p1q1 * 'X^(2 * m) + (p12q12 - p1q1 - p2q2) * 'X^m + p2q2
  end.

Definition karatsuba p q :=
  let (p1,q1) := if size p < size q then (q,p) else (p,q) in
  karatsuba_rec (size p1) p1 q1.

Lemma karatsuba_recP : forall n p q, karatsuba_rec n p q = p * q.
Proof.
elim=> // n ih p q /=.
case: ifP=> // _.
set m := minn (size p)./2 (size q)./2.
rewrite {7}(splitP m p) {7}(splitP m q) /= !ih.
set p1 := (Poly (drop m p)); set p2 := (Poly (take m p)).
set q1 := (Poly (drop m q)); set q2 := (Poly (take m q)).
rewrite [(p1 + p2) * _]mulrDl [p1 * (_ + _)]mulrDr [p2 * (_ + _)]mulrDr.
rewrite -!addrA [_ - p2 * q2]addrC addNKr [p1 * _ + _]addrCA [_ - p1 * q1]addrC.
rewrite addNKr mulrDr !mulrDl -!mulrA ['X^m * (q1 * _)]mulrCA -exprD addnn.
by rewrite -mul2n ['X^m * q2]mulrC -!addrA [_ + (_ + p2 * _)]addrCA.
Qed.

Lemma karatsubaP p q : karatsuba p q = p * q.
Proof.
rewrite /karatsuba ltnNge.
wlog -> : p q / size q <= size p=> [H|].
  have [spq|spq] := ltnP; first by move/H: (ltnW spq); rewrite (ltnW spq) mulrC.
  by move/H: (spq); rewrite spq.
by rewrite /= karatsuba_recP.
Qed.


(* seq version *)

(* This is written to reflect Poly *)
Fixpoint take' n (s : seq CR) :=  match n, s with
  | n'.+1, x :: s' => let r := take' n' s'
                      in if size r != 0%N then x :: r else nseq (x != zero CR) x
  | _, _ => [::]
  end.

Lemma last_drop : forall (p : seq R) n, last 1 p != 0 -> last 1 (drop n p) != 0.
Proof.
elim => /= [| x xs ih n h]; first by rewrite oner_neq0.
case: n ih => // n -> //.
case: xs h => //=.
by rewrite oner_neq0.
Qed.

Definition splitp_seq n (p : seq CR) := (drop n p, take' n p).

Lemma splitp_seqE p n :
  (trans (splitp n p).1,trans (splitp n p).2) = splitp_seq n (trans p).
Proof.
rewrite /splitp_seq /=.
apply/pair_eqP/andP => /=.
case: p => p /= h.
split; first by rewrite trans_poly_def (@PolyK _ 1) ?map_drop // last_drop.
rewrite [trans (Polynomial h)]trans_poly_def /=.
apply/eqP; clear h.
elim: p n => [[]|x xs ih n] /=; try by rewrite zeroE.
case: n => [|n] /=; first by rewrite zeroE.
rewrite trans_eq0 -ih size_trans_poly trans_poly_def polyseq_cons polyseqC.
case: ifP => //= _.
by case: (x == 0).
Qed.

Fixpoint karatsuba_rec_seq (n : nat) (p q : seq CR) := match n with
  | 0%N   => mul_seq p q
  | n'.+1 => 
      let sp := size p in let sq := size q in 
      if (sp <= 2) || (sq <= 2) then mul_seq p q else
        let m       := minn (size p)./2 (size q)./2 in
        let (p1,p2) := splitp_seq m p in
        let (q1,q2) := splitp_seq m q in
        let p1q1    := karatsuba_rec_seq n' p1 q1 in
        let p2q2    := karatsuba_rec_seq n' p2 q2 in
        let p12     := add_seq p1 p2 in
        let q12     := add_seq q1 q2 in
        let p12q12  := karatsuba_rec_seq n' p12 q12 in
        add_seq (add_seq (shift (2 * m) p1q1)
                 (shift m (sub_seq (sub_seq p12q12 p1q1) p2q2))) p2q2
  end.

Definition karatsuba_seq (p q : seq CR) :=
  let (p1,q1) := if size p < size q then (q,p) else (p,q) in
  karatsuba_rec_seq (size p1) p1 q1.

Lemma karatsuba_rec_seqE : forall n,
  {morph trans : p q / karatsuba_rec n p q >-> karatsuba_rec_seq n p q}.
Proof.
elim=> /= [|n ih p q]; first exact: mul_seqE.
rewrite !size_trans_poly.
case: ifP=> _; first exact: mul_seqE.
set m := minn (size p)./2 (size q)./2.
case: (splitp_seqE p m) => <- <-.
case: (splitp_seqE q m) => <- <-.
by rewrite -!add_seqE -!ih -!sub_seqE -!shiftE -!add_seqE.
Qed.

Lemma karatsuba_seqE : {morph trans : p q / karatsuba p q >-> karatsuba_seq p q}.
Proof.
move=> p q /=.
rewrite /karatsuba /karatsuba_seq !size_trans_poly.
by case: ifP=> _; rewrite karatsuba_rec_seqE !size_trans_poly.
Qed.

End karatsuba.