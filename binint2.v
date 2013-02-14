(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
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

Import GRing.Theory Num.Theory.  

Section binint_from_pos.

Inductive Z' A B := Z'pos of A | Z'neg of B.
Notation pos := {n : nat | (n > 0)%N}.
Definition posS (n : nat) : pos := exist _ n.+1 isT.

Definition Z'_of_int (m : int) : Z' nat pos := match m with
  | Posz m => Z'pos _ m
  | Negz m => Z'neg _ (posS m)
  end.

Definition int_of_Z' (m : Z' nat pos) : int := match m with
  | Z'pos p => p%:Z
  | Z'neg p => -(val p)%:Z
  end.

Lemma Z'_of_intK : pcancel Z'_of_int (some \o int_of_Z').
Proof. by rewrite /Z'_of_int /int_of_Z' => [[[]|]]. Qed.

Global Instance refinement_int_Z' : refinement int (Z' nat pos) := Refinement Z'_of_intK.

Lemma refines_intE n x : refines n x -> n = int_of_Z' x.
Proof. by case. Qed.

Class embed_class A B := embed_op : A -> B.
Local Notation embed := (@embed_op _).

Section Z'B.
Variable A B : Type.
Notation Z := (Z' A B).

Context `{zero A} `{one A} `{sub A}  `{add A} `{leq A} `{eq A}.
Context `{one B} `{sub B} `{add B} `{eq B}.
Context `{embed_class A B} `{embed_class B A}.

Global Instance zero_Z : zero Z := Z'pos _ 0%C.
Global Instance one_Z : one Z := Z'pos _ 1%C.

Global Instance add_Z : add Z := fun x y : Z =>
match x, y with
| Z'pos x, Z'pos y => Z'pos _ (x + y)%C
| Z'neg x, Z'neg y => Z'neg _ (x + y)%C
| Z'pos x, Z'neg y => if (embed y <= x)%C then Z'pos _ (x - embed y)%C
                      else Z'neg _ (embed (embed y - x)%C)
| Z'neg x, Z'pos y => if (embed x <= y)%C then Z'pos _ (y - embed x)%C
                      else Z'neg _ (embed (embed x - y))%C
end.

Global Instance eq_Z : eq Z := fun x y : Z =>
match x, y with
| Z'pos x, Z'pos y => (x == y)%C
| Z'neg x, Z'neg y =>  (x == y)%C
| _, _ => false
end.

End Z'B.

Section Z'pos.
Notation Z := (Z' nat pos).

Local Instance zero_nat : zero nat := 0%N.
Local Instance one_nat : one nat := 1%N.
Local Instance add_nat : add nat := addn.
Local Instance sub_nat : sub nat := subn.
Local Instance leq_nat : leq nat := ssrnat.leq.
Local Instance eq_nat : eq nat := eqtype.eq_op.

Local Instance one_pos : one pos := posS 0.
Local Instance add_pos : add pos :=
  fun m n => insubd (posS 0) (val m + val n)%N.
Local Instance sub_pos : sub pos :=
  fun m n => insubd (posS 0) (val m - val n)%N.
Local Instance eq_pos : eq pos := eqtype.eq_op.

Local Instance embed_pos_nat : embed_class pos nat := val.
Local Instance embed_nat_pos : embed_class nat pos := insubd 1%C.
 
Global Program Instance refines_int_0 : refines (0%R : int) (0%C : Z).
Global Program Instance refines_int_1 : refines (1%R : int) (1%C : Z).

Global Instance refines_int_add (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x + y) (x' + y')%C.
Proof.
rewrite /refines [x]refines_intE [y]refines_intE /= /add_op.
case: x' y' {rx ry} => [x'|x'] [y'|y'] //=; rewrite ?(add0r, addr0) //;
rewrite /add_op /sub_op /add_pos /sub_pos /embed /embed_pos_nat /embed_nat_pos //;
rewrite /leq_op /leq_nat /sub_nat /add_nat;
do ?by rewrite ?insubdK -?opprD // -?topredE /= ?addn_gt0 ?valP //.
  have [yx|xy] /= := leqP; first by rewrite subzn.
  by rewrite insubdK // -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
have [yx|xy] /= := leqP; first by rewrite addrC subzn.
by rewrite insubdK // -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
Qed. 

Global Instance refines_int_eq (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x == y) (x' == y')%C.
Proof.
rewrite /refines [x]refines_intE [y]refines_intE /= /eq_op => {rx ry}.
case: x' y' => [x'|x'] [y'|y'] //=; rewrite ?eqr_opp // ?[- _ == _]eq_sym;
by rewrite gtr_eqF // (@ltr_le_trans _ 0) // ltr_oppl oppr0 [_ < _]valP.
Qed.

End Z'pos.
