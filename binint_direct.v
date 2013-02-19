(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import ZArith.
Require Import refinements.

(******************************************************************************)
(* The binary integers of Coq is a refinement of SSReflects integers (ssrint) *) 
(*                                                                            *)
(* ??? == some documentation                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.  

Section binint.

Definition Z_of_int (m : int) : Z := match m with
  | Posz m' => Z_of_nat m'
  | Negz m' => (- Z_of_nat m'.+1)%Z
  end.

Definition int_of_Z (m : Z) : int := match m with
  | Z0 => 0
  | Zpos p => (Pos.to_nat p)%:Z
  | Zneg p => (- (Pos.to_nat p)%:Z)
  end.

Lemma Z_of_intK : pcancel Z_of_int (some \o int_of_Z).
Proof.
by rewrite /Z_of_int /int_of_Z => [[[]|]] //= n; rewrite SuccNat2Pos.id_succ.
Qed.

(* mmh ..., not good :-/ *)
Lemma int_of_Z_inj : injective int_of_Z.
Proof.
case=> [|x|x] [|y|y] //=; rewrite -?Pos2Z.opp_pos -!positive_nat_Z.
+ by case: (Pos.to_nat y).  
+ by case: (Pos.to_nat y).  
+ by case: (Pos.to_nat x).
+ by case=> ->.
+ by case: (Pos.to_nat y) (Pos.to_nat x) => [[]|].
+ by case: (Pos.to_nat x).
+ by case: (Pos.to_nat x) (Pos.to_nat y) => [[]|].
+ by case/(can_inj (@opprK _)) => ->.
Qed.

Global Instance refinement_int_Z : refinement int Z := Refinement Z_of_intK.

Lemma refines_intE n x : refines n x -> n = int_of_Z x.
Proof. by case. Qed.

Lemma specZ_inj : injective \spec_int%C.
Proof. by apply: inj_comp; [apply: Some_inj|apply: int_of_Z_inj]. Qed.

(* Constants *)
Global Program Instance zero_Z : zero Z := 0%Z.
Global Program Instance refines_int_0 : refines 0%R 0%Z.

Global Program Instance one_Z : one Z := 1%Z.
Global Program Instance refines_int_1 : refines 1%R 1%Z.

(* Unary operations *)
Global Program Instance opp_Z : opp Z := Z.opp.
Global Program Instance refines_int_opp (x : int) (x' : Z)
  (rx : refines x x') : refines (- x) (- x')%C.
Next Obligation. by elim: x' rx => [|p|p] [/= ->] //; rewrite opprK. Qed.

(* Binary operations *)
Global Program Instance add_Z : add Z := Z.add.
Global Program Instance refines_int_add (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x + y) (x' + y')%C.
Next Obligation.
elim: x' rx => [|p|p] [/= ->]; rewrite ?add0r -?spec_refines //.
  case: y' ry => [|y'|y'] [/= ->]; rewrite ?addr0 //.
    by rewrite Pos2Nat.inj_add.
  rewrite /add_op /add_Z Pos2Z.add_pos_neg.
  case: (Pos.lt_total p y') => [H|[->|H]]; rewrite ?Z.pos_sub_diag ?subrr //.
    rewrite Z.pos_sub_lt //= nat_of_P_minus_morphism ?minusE; last first. 
      by apply/nat_of_P_gt_Gt_compare_complement_morphism/Pos2Nat.inj_lt.
    by rewrite -opprB subzn //; apply/leP/Pos2Nat.inj_le/Pos.lt_le_incl.
  rewrite Z.pos_sub_gt //= nat_of_P_minus_morphism ?minusE; last first. 
    by apply/nat_of_P_gt_Gt_compare_complement_morphism/Pos2Nat.inj_lt.
  by rewrite subzn //; apply/leP/Pos2Nat.inj_le/Pos.lt_le_incl.
case: y' ry => [|y'|y'] [/= ->]; rewrite ?addr0 //; last first.
  by rewrite Pos2Nat.inj_add -opprB opprK addrC. 
rewrite /add_op /add_Z Pos2Z.add_neg_pos.
case: (Pos.lt_total y' p) => [H|[->|H]]; rewrite ?Z.pos_sub_diag addrC ?subrr //.
  rewrite Z.pos_sub_lt //= nat_of_P_minus_morphism ?minusE; last first. 
    by apply/nat_of_P_gt_Gt_compare_complement_morphism/Pos2Nat.inj_lt.
  by rewrite -opprB subzn //; apply/leP/Pos2Nat.inj_le/Pos.lt_le_incl.
rewrite Z.pos_sub_gt //= nat_of_P_minus_morphism ?minusE; last first. 
  by apply/nat_of_P_gt_Gt_compare_complement_morphism/Pos2Nat.inj_lt.
by rewrite subzn //; apply/leP/Pos2Nat.inj_le/Pos.lt_le_incl.
Qed. (* TODO: Simplify *)

Global Program Instance sub_Z : sub Z := Z.sub.
Global Program Instance refines_int_sub (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x - y) (x' - y')%C.
Next Obligation.
by rewrite /sub_op /sub_Z -Z.add_opp_r [x - y]refines_intE.
Qed.

Global Program Instance mul_Z : mul Z := Z.mul.
Global Program Instance refines_int_mul (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x * y) (x' * y')%C. 
Next Obligation. Admitted.

(* Comparison operations *)
Global Program Instance eq_Z : eq Z := Z.eqb.
Global Instance refines_int_eq (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x == y) (x' == y')%C.
Proof.
rewrite /refines /eq_op /eq_Z; congr Some.
apply/idP/idP => [/eqP h|].
  by apply/Z.eqb_eq/specZ_inj; rewrite !spec_refines h.
case: (Z.eqb_spec _ _) => h // _.
by apply/eqP/Some_inj; rewrite -!spec_refines h.    
Qed.

Global Program Instance leq_Z : leq Z := Z.leb.
Global Program Instance refines_int_leq (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x <= y) (x' <= y')%C.
Next Obligation. Admitted.

Global Program Instance lt_Z : lt Z := Z.ltb.
Global Program Instance refines_int_lt (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x < y) (x' < y')%C.
Next Obligation. Admitted.

End binint.

(* (* Some tests *) *)
(* Eval compute in 0%C. *)
(* Eval compute in (1 + 1 * 1 + 1)%C. *)