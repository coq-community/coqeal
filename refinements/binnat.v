Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
Require Import NArith.

Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op.

(* Bin nat refines ssr nat *)
Section binnat_op.

Global Instance zero_N : zero_of N := N.zero.
Global Instance one_N  : one_of N  := N.one.
Global Instance add_N  : add_of N  := N.add.
Global Instance eq_N   : eq_of N  := N.eqb.
Global Instance spec_N : spec_of N nat := nat_of_bin.
Global Instance implem_N : implem_of nat N := bin_of_nat.

End binnat_op.

Section binnat_theory.

Local Open Scope rel_scope.

Definition Rnat : nat -> N -> Type := fun n n' => n = nat_of_bin n'.

Global Instance Rnat_0 : refines Rnat 0%nat 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_1 : refines Rnat 1%nat 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_add :
  refines (Rnat ==> Rnat ==> Rnat) (fun m n => m + n)%nat +%C.
Proof. by rewrite !refinesE=> m m' -> n n' ->; rewrite -nat_of_add_bin. Qed.

Global Instance Rnat_eq : refines (Rnat ==> Rnat ==> bool_R) eqtype.eq_op eq_op.
Proof.
rewrite !refinesE=> m m' -> n n' ->; rewrite /eq_op /eq_N.
case: (N.eqb_spec _ _) => [->|/eqP hneq].
  by rewrite eqxx; exact: true_R.
suff H : (nat_of_bin m' == nat_of_bin n') = false.
  by rewrite H; exact: false_R.
by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

End binnat_theory.

Section testnat.

Local Instance Rnat_implem n : refines Rnat n (implem n) | 999.
Proof. by rewrite refinesE /Rnat /implem /implem_N bin_of_natK. Qed.

Goal (1 == 1)%nat.
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (100 == 100)%nat.
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (998 + 2 == 1000)%nat.
rewrite [_ == _]refines_eq.
by compute.
Abort.

End testnat.
