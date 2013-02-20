Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic. 

Section generic_karatsuba.

Variable polyA : Type.
Context `{add polyA, mul polyA, sub polyA}.
Variable shift_polyA : nat -> polyA -> polyA.
Variable size_polyA : polyA -> nat.
Variable splitp_polyA : nat -> polyA -> polyA * polyA.

Fixpoint karatsuba_rec (n : nat) (p q : polyA) := match n with
  | 0%N   => (p * q)%C
  | n'.+1 => 
      let sp := size_polyA p in let sq := size_polyA q in 
      if (sp <= 2) || (sq <= 2) then (p * q)%C else
        let m       := minn sp./2 sq./2 in
        let (p1,p2) := splitp_polyA m p in
        let (q1,q2) := splitp_polyA m q in
        let p1q1    := karatsuba_rec n' p1 q1 in
        let p2q2    := karatsuba_rec n' p2 q2 in
        let p12     := (p1 + p2)%C in
        let q12     := (q1 + q2)%C in
        let p12q12  := karatsuba_rec n' p12 q12 in
        (shift_polyA (2 * m)%N p1q1 +
         shift_polyA m (p12q12 - p1q1 - p2q2) +
         p2q2)%C
  end.

Definition karatsuba p q :=
  karatsuba_rec (maxn (size_polyA p) (size_polyA q)) p q.

End generic_karatsuba.

Section karatsuba_poly.

Variable R : ringType.
Instance add_polyR : add {poly R} := +%R.
Instance mul_polyR : mul {poly R} := *%R.
Instance sub_polyR : sub {poly R} := fun x y => (x - y)%R.
Variable f : {poly R} -> nat.
Definition karatsuba_recR :=
  (karatsuba_rec (fun n => *%R^~ 'X^n) f
                 (fun n p => (rdivp p 'X^n, rmodp p 'X^n))).
Notation karatsubaR :=
  (karatsuba (fun n => *%R^~ 'X^n) f
             (fun n p => (rdivp p 'X^n, rmodp p 'X^n))).

Lemma karatsuba_recE n (p q : {poly R}) : karatsuba_recR n p q = p * q.
Proof.
elim: n=> //= n ih in p q *; case: ifP=> // _; set m := minn _ _.
rewrite [p in RHS](rdivp_eq (monicXn _ m)) [q in RHS](rdivp_eq (monicXn _ m)).
rewrite !ih !(mulrDl, mulrDr, mulNr) mulnC exprM.
rewrite -addrA -opprD [X in X + _ - _]addrC addrACA addrK.
by simpC; rewrite !(commr_polyXn, mulrA, addrA).
Qed.

Lemma karatsubaP (p q : {poly R}) : karatsubaR p q = p * q.
Proof. exact: karatsuba_recE. Qed.

End karatsuba_poly.

