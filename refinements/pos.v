(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
From CoqEAL Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op GRing.Theory.

Record pos := pos_of {
                  val_of_pos : nat;
                  _ : (val_of_pos > 0)%N
                }.
Canonical pos_subType := [subType for val_of_pos].

Definition pos_eqMixin := [eqMixin of pos by <:].
Canonical pos_eqType := EqType pos pos_eqMixin.

(* Parametricity pos. *)

(* Lemma eq_bool_R x y (a b : bool_R x y) : a = b. *)
(* Proof. Admitted. *)

(* Lemma pos_Rxx p : pos_R p p. *)
(* Proof. *)
(*   case: p=> n ngt0. *)
(*   apply: (@pos_R_pos_of_R _ _ (nat_Rxx _)). *)
(*   case: _ / ngt0 (leq_R _ _) bool_R_true_R=> a b. *)
(*   rewrite [a](eq_bool_R _ b). *)
(*   by constructor. *)
(* Qed. *)

Section pos.

Import Refinements.Op.

Definition posS (n : nat) : pos := @pos_of n.+1 isT.

#[export] Instance pos1    : one_of pos := posS 0.
#[export] Instance add_pos : add_of pos := fun m n => insubd pos1 (val m + val n).
#[export] Instance sub_pos : sub_of pos := fun m n => insubd pos1 (val m - val n).
#[export] Instance mul_pos : mul_of pos := fun m n => insubd pos1 (val m * val n).
#[export] Instance exp_pos : exp_of pos pos :=
  fun m n => insubd pos1 (val m ^ val n).
#[export] Instance leq_pos : leq_of pos := fun m n => val m <= val n.
#[export] Instance lt_pos  : lt_of pos  := fun m n => val m < val n.
#[export] Instance eq_pos  : eq_of pos  := eqtype.eq_op.

#[export] Instance cast_pos_nat : cast_of pos nat := val.
#[export] Instance cast_nat_pos : cast_of nat pos := insubd 1%C.

Local Open Scope ring_scope.
Definition pos_to_int (p : pos) : int := (val p)%:R.
Definition int_to_nat (z : int) : nat := if z > 0 then `|z|%N else 0%N.
Definition int_to_pos (z : int) : pos := insubd pos1 (int_to_nat z).

End pos.