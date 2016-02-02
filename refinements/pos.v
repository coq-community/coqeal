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

Notation pos := {n : nat | (n > 0)%N}.

Section pos.

Import Refinements.Op.

Definition pos_of (n : nat) (n_gt0 : n > 0) : pos := exist _ n n_gt0.
Definition posS (n : nat) : pos := @pos_of n.+1 isT.

Instance pos1    : one_of pos := posS 0.
Instance add_pos : add_of pos := fun m n => insubd pos1 (val m + val n).
Instance sub_pos : sub_of pos := fun m n => insubd pos1 (val m - val n).
Instance mul_pos : mul_of pos := fun m n => insubd pos1 (val m * val n).
(*Instance exp_pos : exp_of pos pos := fun m n => insubd pos1 (val m ^ val n).*)
Instance leq_pos : leq_of pos := fun m n => val m <= val n.
(*Instance lt_pos  : lt_of pos  := fun m n => val m < val n.*)
Instance eq_pos  : eq_of pos  := eqtype.eq_op.

Instance cast_pos_nat : cast_of pos nat := val.
Instance cast_nat_pos : cast_of nat pos := insubd 1%C.

Local Open Scope ring_scope.
Definition pos_to_int (p : pos) : int := (val p)%:R.
Definition int_to_nat (z : int) : nat := if z > 0 then `|z|%N else 0%N.
Definition int_to_pos (z : int) : pos := insubd pos1 (int_to_nat z).

End pos.
