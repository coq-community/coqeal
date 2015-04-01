Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
Require Import ssrint ZArith.

Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

Local Open Scope ring_scope.

Section binint_op.

Definition int_of_Z (n : Z) : int := match n with
  | Z0 => Posz 0
  | Zpos p => Posz (nat_of_pos p)
  | Zneg p => Negz (nat_of_pos p).-1
  end.

Definition Z_of_int (n : int) : Z := match n with
  | Posz n => Z.of_nat n
  | Negz n => - (Z.of_nat n.+1)
  end.

Global Instance zero_Z : zero_of Z := Z.zero.
Global Instance one_Z  : one_of Z  := Z.one.
Global Instance add_Z  : add_of Z  := Z.add.
Global Instance mul_Z  : mul_of Z  := Z.mul.
Global Instance opp_Z  : opp_of Z  := Z.opp.
Global Instance eq_Z   : eq_of Z   := Z.eqb.

Global Instance spec_Z : spec_of Z int := int_of_Z.
Global Instance implem_Z : implem_of int Z := Z_of_int.

End binint_op.

Section binint_theory.

Local Open Scope rel_scope.

Definition Rint : int -> Z -> Type := fun n n' => n = int_of_Z n'.

Global Instance Rint_0 : refines Rint 0 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rint_1 : refines Rint 1 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rint_opp : refines (Rint ==> Rint) -%R -%C.
Admitted.

Global Instance Rint_add : refines (Rint ==> Rint ==> Rint) +%R +%C.
Admitted.

Global Instance Rint_mul : refines (Rint ==> Rint ==> Rint) *%R *%C.
Admitted.

Global Instance Rint_eq : refines (Rint ==> Rint ==> bool_R) eqtype.eq_op eq_op.
Admitted.

Global Instance Rint_implem n : refines Rint n (implem n) | 999.
Admitted.

End binint_theory.

Section testint.

Goal (1 == 1 :> int).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (10%:Z - 5%:Z == 1 + 4%:Z).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (1000%:Z == 998%:Z + 2%:Z).
rewrite [_ == _]refines_eq.
by compute.
Abort.

End testint.
