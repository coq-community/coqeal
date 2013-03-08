(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements.

(******************************************************************************)
(* Attempt to refine SSReflect integers (ssrint) are to a new type            *)
(* paremetrized by positive numbers (represented by a sigma type) and natural *)
(* numbers. This gives simpler proofs than in binint, but in order for this   *)
(* to be useful the parametricity part of the library must be used to change  *)
(* the representation of positive numbers and naturals to more efficient      *)
(* representations (e.g. N) which has not been done yet.                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Num.Theory Refinements.Op.

(* Programming part *)
Section Zdef.
Variable N P : Type.
Inductive Z := Zpos of N | Zneg of P.

Local Open Scope computable_scope.

Context `{zero N, one N, sub N, add N, mul N, leq N, eq N}.
Context `{one P, sub P, add P, mul P, eq P}.
Context `{embed_class N P, embed_class P N}.

Global Instance zero_Z : zero Z := Zpos 0.
Global Instance one_Z : one Z := Zpos 1.

Global Instance add_Z : add Z := fun x y : Z =>
match x, y with
| Zpos x, Zpos y => Zpos (x + y)
| Zneg x, Zneg y => Zneg (x + y)
| Zpos x, Zneg y => if (embed y <= x) then Zpos (x - embed y)
                      else Zneg (embed (embed y - x))
| Zneg x, Zpos y => if (embed x <= y) then Zpos (y - embed x)
                      else Zneg (embed (embed x - y))
end.

Global Instance opp_Z : opp Z := fun x : Z =>
match x with
| Zpos x => if (x == 0)%C then 0%C else Zneg (embed x)
| Zneg x => Zpos (embed x)
end.

Global Instance sub_Z : sub Z := fun x y : Z =>
match x, y with
| Zpos x, Zneg y => Zpos (x + embed y)
| Zneg x, Zpos y => if (y == 0)%C then Zneg x else Zneg (x + embed y)
| Zpos x, Zpos y => if (y <= x) then Zpos (x - y)
                      else Zneg (embed (y - x))
| Zneg x, Zneg y => if (embed x <= embed y) then Zpos (embed y - embed x)
                      else Zneg (embed (embed x - embed y))
end.

Global Instance eq_Z : eq Z := fun x y : Z =>
match x, y with
| Zpos x, Zpos y => (x == y)
| Zneg x, Zneg y => (x == y)
| _, _ => false
end.

Global Instance mul_Z : mul Z := fun x y : Z =>
match x, y with
| Zpos x, Zpos y => Zpos (x * y)
| Zneg x, Zpos y => if (y == 0)%C then 0%C else Zneg (x * embed y)
| Zpos x, Zneg y => if (x == 0)%C then 0%C else Zneg (embed x * y)
| Zneg x, Zneg y => Zpos (embed x * embed y)
end.

Global Instance embed_N_Z : embed_class N Z :=
  fun n : N => Zpos n.

Global Instance embed_P_Z : embed_class P Z :=
  fun n : P => Zpos (embed n).

End Zdef.

(* Proof part, should be refactored *)
Section Z_nat_pos.

Notation pos := {n : nat | (n > 0)%N}.
Definition posS (n : nat) : pos := exist _ n.+1 isT.

Notation Z := (Z nat pos).

Definition Z_of_int (m : int) : Z := match m with
  | Posz m => Zpos _ m
  | Negz m => Zneg _ (posS m)
  end.

Definition int_of_Z (m : Z) : int := match m with
  | Zpos p => p%:Z
  | Zneg p => -(val p)%:Z
  end.

Lemma Z_of_intK : pcancel Z_of_int (some \o int_of_Z).
Proof. by rewrite /Z_of_int /int_of_Z => [[[]|]]. Qed.

Global Instance refinement_int_Z : refinement int Z := Refinement Z_of_intK.

Lemma refines_intE n x : refines n x -> n = int_of_Z x.
Proof. by case. Qed.

Local Instance zero_nat : zero nat := 0%N.
Local Instance one_nat : one nat := 1%N.
Local Instance add_nat : add nat := addn.
Local Instance sub_nat : sub nat := subn.
Local Instance mul_nat : mul nat := muln.
Local Instance leq_nat : leq nat := ssrnat.leq.
Local Instance eq_nat : eq nat := eqtype.eq_op.

Local Instance one_pos : one pos := posS 0.
Local Instance add_pos : add pos :=
  fun m n => insubd (posS 0) (val m + val n)%N.
Local Instance sub_pos : sub pos :=
  fun m n => insubd (posS 0) (val m - val n)%N.
Local Instance mul_pos : mul pos :=
  fun m n => insubd (posS 0) (val m * val n)%N.
Local Instance eq_pos : eq pos := eqtype.eq_op.

Local Instance embed_pos_nat : embed_class pos nat := val.
Local Instance embed_nat_pos : embed_class nat pos := insubd 1%C.
 
Global Program Instance refines_int_0 : refines (0%R : int) (0%C : Z).
Global Program Instance refines_int_1 : refines (1%R : int) (1%C : Z).

Global Instance refines_int_add (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x + y) (x' + y')%C.
Proof.
rewrite /refines [x]refines_intE [y]refines_intE /add_op /=.
case: x' y' {rx ry} => [x'|x'] [y'|y'] //=; rewrite ?(add0r, addr0) //; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [yx|xy] /= := leqP; first by rewrite addrC subzn.
  by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
by rewrite !insubdK -?topredE /= ?addn_gt0 ?valP // -opprB opprK addrC.
Qed. 

Global Instance refines_int_opp (x : int) (x' : Z)
  (rx : refines x x') : refines (- x) (- x')%C.
Proof.
rewrite [x]refines_intE; congr some.
by case: x' {rx} => [[]|] //= n; rewrite ?insubdK ?opprK.
Qed.

Global Instance refines_int_sub (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x - y) (x' - y')%C.
Proof.
rewrite [x]refines_intE [y]refines_intE /sub_op; congr some.
case: x' y' {rx ry} => [x'|x'] [y'|y']; rewrite ?opprK //=; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [->|y'_neq0 /=] := (altP eqP); first by rewrite subr0.
  by rewrite !insubdK -?opprD -?topredE //= ?addn_gt0 ?valP ?lt0n.
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

Global Instance refines_int_mul (x y : int) (x' y' : Z)
  (rx : refines x x') (ry : refines y y') : refines (x * y) (x' * y')%C.
Proof.
rewrite /refines [x]refines_intE [y]refines_intE /mul_op /=; congr some.
case: x' y' {rx ry} => [x'|x'] [y'|y'] //=; simpC; last by rewrite mulrNN.
  have [->|y'_neq0 /=] := (altP eqP); first by rewrite mul0r.
  by rewrite mulrN !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
have [->|y'_neq0 /=] := (altP eqP); first by rewrite mulr0.
by rewrite mulNr !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
Qed. 

End Z_nat_pos.