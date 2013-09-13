(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

Notation pos := {n : nat | (n > 0)%N}.

Section pos.

Import Refinements.Op.

Definition posS (n : nat) : pos := exist _ n.+1 isT.

Instance pos1    : one pos := posS 0.
Instance add_pos : add pos := fun m n => insubd pos1 (val m + val n).
Instance sub_pos : sub pos := fun m n => insubd pos1 (val m - val n).
Instance mul_pos : mul pos := fun m n => insubd pos1 (val m * val n).
Instance leq_pos : leq pos := fun m n => val m <= val n.
Instance lt_pos  : lt pos  := fun m n => val m < val n.
Instance eq_pos  : eq pos  := eqtype.eq_op.

Instance cast_pos_nat : cast_class pos nat := val.
Instance cast_nat_pos : cast_class nat pos := insubd 1%C.

End pos.
