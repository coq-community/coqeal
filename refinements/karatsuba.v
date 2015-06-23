Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

Require Import hrel param refinements seqpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op.

Local Open Scope ring_scope.
Local Open Scope rel.

(* Classes for karatsuba *)
Section classes.

Class shift_of polyA := shift_op : nat -> polyA -> polyA.
Class split_of polyA := split_op : nat -> polyA -> polyA * polyA.

End classes.

Section generic_karatsuba.

Variable polyA : Type.

Context `{add_of polyA, mul_of polyA, sub_of polyA}.
Context `{shift_poly : shift_of polyA, size_poly : size_of polyA}.
Context `{split_poly : split_of polyA}.

Fixpoint karatsuba_rec n (p q : polyA) := match n with
  | 0     => (p * q)%C
  | n'.+1 => 
      let sp := size_poly p in let sq := size_poly q in 
      if (sp <= 2)%nat || (sq <= 2)%nat then (p * q)%C else
        let m       := minn sp./2 sq./2 in
        let (p1,p2) := split_poly m p in
        let (q1,q2) := split_poly m q in
        let p1q1    := karatsuba_rec n' p1 q1 in
        let p2q2    := karatsuba_rec n' p2 q2 in
        let p12     := (p1 + p2)%C in
        let q12     := (q1 + q2)%C in
        let p12q12  := karatsuba_rec n' p12 q12 in
        (shift_poly (2 * m)%nat p1q1 +
         shift_poly m (p12q12 - p1q1 - p2q2) +
         p2q2)%C
  end.

Definition karatsuba p q :=
  karatsuba_rec (maxn (size_poly p) (size_poly q)) p q.

End generic_karatsuba.

Parametricity karatsuba.
Parametricity karatsuba_rec.

Section karatsuba_theory.

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

(* Give this higher priority than the instance for mul_seqpoly so that it
   gets found instead *)
Global Instance RpolyC_karatsuba_mul :
  refines (RpolyC ==> RpolyC ==> RpolyC) *%R (karatsuba (polyA:=polyC)) | 0.
Proof.
by rewrite refinesE; do?move=> ?*; rewrite -karatsubaE; apply: refinesP; tc.
Qed.

End karatsuba_param.
End karatsuba_theory.

Section seqpoly_karatsuba.

Section op.

Variable C : Type.

Context `{zero_of C}.

Global Instance shift : shift_of (seqpoly C) := fun n => ncons n 0%C.
(* Arguments shift n p : simpl nomatch. *)

Global Instance split_seqpoly : split_of (seqpoly C) := fun n p => 
  (take n p,drop n p).

End op.

Parametricity shift.
Parametricity split_seqpoly.

Section correctness.

Variable R : ringType.
Instance : zero_of R := 0.

(* These can be done with Logic.eq instead of nat_R *)
Instance Rseqpoly_shift :
  refines (Logic.eq ==> @Rseqpoly R ==> @Rseqpoly R) (@shiftp R) shift_op.
Admitted.

Instance Rseqpoly_split :
  refines (Logic.eq ==> @Rseqpoly R ==> prod_hrel (@Rseqpoly R) (@Rseqpoly R))
    (@splitp R) split_op.
Admitted.

Section param.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, !refines rAC 0%R 0%C}.

(* This should use nat_R and not Logic.eq *)
Global Instance RseqpolyC_shift :
  refines (nat_R ==> RseqpolyC rAC ==> RseqpolyC rAC) (@shiftp R) shift_op.
Proof. param_comp shift_R. Qed.

(* Uses composable_prod *)
Global Instance RseqpolyC_split :
  refines (nat_R ==> RseqpolyC rAC ==> prod_R (RseqpolyC rAC) (RseqpolyC rAC))
    (@splitp R) split_op.
Proof. param_comp split_seqpoly_R. Qed.

End param.
End correctness.
End seqpoly_karatsuba.

Section test_karatsuba.

Require Import ssrint binint.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999. 
Proof. by rewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed.

(* Test shiftp *)
Goal (2%:Z *: shiftp 2%nat 1 == Poly [:: 0; 0; 2%:Z]).
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

Let p1 := Eval compute in bigseq 1 10.
Let p2 := Eval compute in bigseq 2 10.

(* TODO: Translate Poly directly? *)
Goal (Poly p1 * Poly p2 == Poly p2 * Poly p1).
rewrite [_ == _]refines_eq.
by compute.
Abort.

End test_karatsuba.
