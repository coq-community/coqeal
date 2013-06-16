Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* factor this out !*)
Notation pos := {n : nat | (n > 0)%N}.

Section positive.
Import Refinements.Op.
Definition posS (n : nat) : pos := exist _ n.+1 isT.
Local Instance pos1 : one pos := posS 0.
Local Instance add_pos : add pos := fun m n => insubd pos1 (val m + val n).
Local Instance sub_pos : sub pos := fun m n => insubd pos1 (val m - val n).
Local Instance mul_pos : mul pos := fun m n => insubd pos1 (val m * val n).
Local Instance leq_pos : leq pos := fun m n => val m <= val n.
Local Instance lt_pos : lt pos := fun m n => val m < val n.
End positive.
