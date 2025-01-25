From elpi Require Import derive.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset bigop poly polydiv.

From CoqEAL Require Import param.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.

(* Specific classes for polynomials *)
Module Poly.
Module Op.

Class shift_of polyA N := shift_op : N -> polyA -> polyA.
#[export] Hint Mode shift_of + + : typeclass_instances.
Class split_of polyA N := split_op : N -> polyA -> polyA * polyA.
#[export] Hint Mode split_of + + : typeclass_instances.
Class lead_coef_of A polyA := lead_coef_op : polyA -> A.
#[export] Hint Mode lead_coef_of + + : typeclass_instances.
Class scal_of polyA N := scal_op : polyA -> polyA -> N.
#[export] Hint Mode scal_of + + : typeclass_instances.

Elpi derive.param2 shift_of.
Elpi derive.param2 shift_op.
Elpi derive.param2 split_of.
Elpi derive.param2 split_op.
Elpi derive.param2 lead_coef_of.
Elpi derive.param2 lead_coef_op.
Elpi derive.param2 scal_of.
Elpi derive.param2 scal_op.

End Op.
End Poly.

Import Poly.Op.

#[export] Typeclasses Transparent shift_of split_of lead_coef_of scal_of.

Section poly_op.

Local Open Scope ring_scope.

Variable R : ringType.

Definition splitp : nat -> {poly R} -> {poly R} * {poly R} :=
  fun n p => (rdivp p 'X^n, rmodp p 'X^n).

Definition shiftp n (p : {poly R}) := p * 'X^n.

Definition sizep : {poly R} -> nat := size.
Lemma sizepE s : sizep s = size s. Proof. by []. Qed.

End poly_op.
