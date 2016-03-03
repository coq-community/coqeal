From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

From CoqEAL Require Import hrel param refinements seqpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op.

Local Open Scope ring_scope.
Local Open Scope rel.

Section karatsuba_generic.

Variable polyA : Type.

Context `{add_of polyA, mul_of polyA, sub_of polyA}.
Context `{shiftp : shift_of polyA, sizep : size_of polyA}.
Context `{splitp : split_of polyA}.

Fixpoint karatsuba_rec n (p q : polyA) := match n with
  | 0     => (p * q)%C
  | n'.+1 =>
      let sp := sizep p in let sq := sizep q in
      if (sp <= 2)%nat || (sq <= 2)%nat then (p * q)%C else
        let m       := minn sp./2 sq./2 in
        let (p1,p2) := splitp m p in
        let (q1,q2) := splitp m q in
        let p1q1    := karatsuba_rec n' p1 q1 in
        let p2q2    := karatsuba_rec n' p2 q2 in
        let p12     := (p1 + p2)%C in
        let q12     := (q1 + q2)%C in
        let p12q12  := karatsuba_rec n' p12 q12 in
        (shiftp (2 * m)%nat p1q1 +
         shiftp m (p12q12 - p1q1 - p2q2) +
         p2q2)%C
  end.

Definition karatsuba p q :=
  karatsuba_rec (maxn (sizep p) (sizep q)) p q.

End karatsuba_generic.

Parametricity karatsuba_rec.
Parametricity karatsuba.

Section karatsuba_correctness.

Local Open Scope rel_scope.

Variable R : ringType.

Definition splitp : nat -> {poly R} -> {poly R} * {poly R} :=
  fun n p => (rdivp p 'X^n, rmodp p 'X^n).

Definition shiftp n (p : {poly R}) := p * 'X^n.

Instance add_polyR : add_of {poly R} := +%R.
Instance mul_polyR : mul_of {poly R} := *%R.
Instance sub_polyR : sub_of {poly R} := fun x y => (x - y)%R.
Instance size_polyR : size_of {poly R} := sizep (R:=R).
Instance shift_polyR : shift_of {poly R} := shiftp.
Instance split_polyR : split_of {poly R} := splitp.

Lemma karatsuba_recE n (p q : {poly R}) : karatsuba_rec n p q = p * q.
Proof.
elim: n=> //= n ih in p q *; case: ifP=> // _; set m := minn _ _.
rewrite [p in RHS](rdivp_eq (monicXn _ m)) [q in RHS](rdivp_eq (monicXn _ m)).
rewrite /shift_op /shift_polyR /shiftp.
rewrite !ih !(mulrDl, mulrDr, mulNr) mulnC exprM.
rewrite -addrA -opprD [X in X + _ - _]addrC addrACA addrK.
by simpC; rewrite !(commr_polyXn, mulrA, addrA).
Qed.

Lemma karatsubaE (p q : {poly R}) : karatsuba p q = p * q.
Proof. exact: karatsuba_recE. Qed.

Section karatsuba_param.

Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).
Context `{add_of polyC, mul_of polyC, sub_of polyC}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) +%R +%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) *%R *%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) (fun x y => x - y)%R sub_op}.

Context `{!shift_of polyC}.
Context `{!refines (nat_R ==> RpolyC ==> RpolyC) shift_polyR shift_op}.

Context `{!size_of polyC}.
Context `{!refines (RpolyC ==> nat_R) size_polyR size_op}.

Context `{!split_of polyC}.
Context `{!refines (nat_R ==> RpolyC ==> prod_R RpolyC RpolyC) split_polyR split_op}.

Global Instance RpolyC_karatsuba_rec :
  refines (nat_R ==> RpolyC ==> RpolyC ==> RpolyC)
    (karatsuba_rec (polyA:={poly R})) (karatsuba_rec (polyA:=polyC)).
Proof. param karatsuba_rec_R. Qed.

Global Instance RpolyC_karatsuba :
  refines (RpolyC ==> RpolyC ==> RpolyC)
    (karatsuba (polyA:={poly R})) (karatsuba (polyA:=polyC)).
Proof. param karatsuba_R. Qed.

Global Instance RpolyC_karatsuba_mul p sp q sq :
  refines RpolyC p sp -> refines RpolyC q sq ->
  refines RpolyC (p * q) (karatsuba sp sq).
Proof.
  move=> hp hq.
  rewrite refinesE -karatsubaE.
  apply: refinesP.
Qed.

End karatsuba_param.
End karatsuba_correctness.

Section karatsuba_test.

From mathcomp Require Import ssrint.
From CoqEAL Require Import binint.

Goal ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X) == 1 + 4%:Z *: 'X + 4%:Z%:P * 'X^2).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z] * Poly [:: 1; 2%:Z]) == Poly [:: 1; 4%:Z; 4%:Z].
rewrite [_ == _]refines_eq.
by compute.
Abort.

Fixpoint bigseq (x : int) (n : nat) : seq int := match n with
  | 0 => [:: x]
  | n'.+1 => x :: bigseq (x+1) n'
  end.

Fixpoint bigpoly (x : int) (n : nat) : {poly int} :=
  match n with
  | 0 => x%:P
  | n.+1 => x%:P + (bigpoly (x+1) n) * 'X
  end.

Let p1 := Eval compute in bigseq 1 10.
Let p2 := Eval compute in bigseq 2 10.

Let q1 := Eval simpl in bigpoly 1 10.
Let q2 := Eval simpl in bigpoly 2 10.

(* TODO: Translate Poly directly? *)
Goal (Poly p1 * Poly p2 == Poly p2 * Poly p1).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (q1 * q2 == q2 * q1).
rewrite [_ == _]refines_eq.
by compute.
Abort.

End karatsuba_test.
