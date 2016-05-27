Require Import ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

From CoqEAL Require Import hrel param refinements binnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Refinements.Op zmodp.

Local Open Scope ring_scope.

Section binord_op.

Definition binord := fun (_ : nat) => N.

Global Instance zero_ord n : zero_of (binord n) := N.zero.

Global Instance one_ord n : one_of (binord n.+1) :=
  if (n == 0)%N then N.zero else N.one.

Global Instance opp_ord n : opp_of (binord n) :=
  fun x => N.modulo ((implem n) - x) (implem n).

Global Instance add_ord n : add_of (binord n) :=
  fun x y => N.modulo (x + y) (implem n).

Global Instance sub_ord n : sub_of (binord n) :=
  fun x y => N.modulo (x + (N.modulo ((implem n) - y) (implem n))) (implem n).

Global Instance mul_ord n : mul_of (binord n) :=
  fun x y => N.modulo (x * y) (implem n).

Global Instance exp_ord n : exp_of (binord n) N :=
  fun x y => N.modulo (x ^ y) (implem n).

Global Instance eq_ord n : eq_of (binord n) := N.eqb.

Global Instance leq_ord n : leq_of (binord n) := N.leb.

Global Instance lt_ord n : lt_of (binord n) := N.ltb.

Global Instance implem_ord n : implem_of 'I_n (binord n) :=
  fun x => implem (x : nat).

End binord_op.

Section binord_theory.

Local Open Scope rel_scope.

Definition Rord n1 n2 (rn : nat_R n1 n2) : 'I_n1 -> binord n2 -> Type :=
  fun x y => Rnat x y.

Global Instance Rord_0 n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn)) 0%R 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rord_1 n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn)) Zp1 1%C.
Proof.
  rewrite refinesE /Rord /Zp1 /inZp /= modn_def (nat_R_eq rn).
  by case: n2 rn.
Qed.

Local Instance refines_nat_R_S n1 n2 :
  refines nat_R n1 n2 -> refines nat_R n1.+1 n2.+1.
Proof. rewrite refinesE; exact: nat_R_S_R. Qed.

Local Instance refines_implem_eq A B (R : A -> B -> Type)
      `{implem_of A B, !refines (eq ==> R) implem_id implem} x y :
  refines eq x y -> refines R x (implem y).
Proof.
  move=> eqxy.
  rewrite -[x]/(implem_id _).
  exact: refines_apply.
Qed.

Local Arguments Rord /.
Local Arguments opp_op /.
Local Arguments opp_ord /.
Local Arguments N.sub : simpl nomatch.

Global Instance Rord_opp n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn)) -%R -%C.
Proof.
  rewrite refinesE=> x x' hx /=.
  exact: refinesP.
Qed.

Local Arguments add_op /.
Local Arguments add_ord /.

Global Instance Rord_add n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn))
          +%R +%C.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  exact: refinesP.
Qed.

Local Arguments sub_op /.
Local Arguments sub_ord /.

Global Instance Rord_sub n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn))
          (fun x y => x - y) sub_op.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  exact: refinesP.
Qed.

Local Arguments mul_op /.
Local Arguments mul_ord /.

Global Instance Rord_mul n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn))
          (@Zp_mul n1) *%C.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  exact: refinesP.
Qed.

Local Arguments eq_op /.
Local Arguments eq_ord /.

Global Instance Rord_eq n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          eqtype.eq_op eq_op.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  have -> : (x == y) = (x == y :> nat) by [].
  exact: refinesP.
Qed.

Local Arguments leq_op /.
Local Arguments leq_ord /.

Global Instance Rord_leq n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          (fun x y => (x <= y)%N) leq_op.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  exact: refinesP.
Qed.

Local Arguments lt_op /.
Local Arguments lt_ord /.
Local Opaque ltn.

Global Instance Rord_lt n1 n2 (rn : nat_R n1 n2) :
  refines (Rord (nat_R_S_R rn) ==> Rord (nat_R_S_R rn) ==> bool_R)
          (fun x y => ltn x y) lt_op.
Proof.
  rewrite refinesE=> x x' hx y y' hy /=.
  exact: refinesP.
Qed.

Local Arguments implem_id /.
Local Arguments implem /.
Local Arguments implem_ord /.

Global Instance Rord_implem n1 n2 (rn : nat_R n1 n2) :
  refines (ordinal_R rn ==> Rord rn) implem_id implem.
Proof.
  rewrite refinesE=> x y rxy /=.
  rewrite -[implem_N]/implem.
  have hxy : refines eq (nat_of_ord x) (nat_of_ord y).
    rewrite refinesE.
    case: rxy=> m1 m2 rm _ _ _ /=.
    by rewrite (nat_R_eq rm).
  exact: refinesP.
Qed.

Global Instance Rnat_nat_of_ord n1 n2 (rn : nat_R n1 n2) :
  refines (Rord rn ==> Rnat) (@nat_of_ord n1) id.
Proof. by rewrite refinesE. Qed.

End binord_theory.