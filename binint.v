(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements pos.

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

Import GRing.Theory Num.Theory Refinements.

(******************************************************************************)
(** PART I: Defining generic datastructures and programming with them         *)
(******************************************************************************)
Section binint_op.
Variable N P : Type.

Import Op AlgOp.
Local Open Scope computable_scope.

Inductive Z := Zpos of N | Zneg of P.

Definition Zmatch T (n : Z) f g : T :=
   match n with Zpos p => f p | Zneg n => g n end.

Context `{zero N, one N, sub N, add N, mul N, leq N, eq N}.
Context `{one P, sub P, add P, mul P, eq P}.
Context `{cast_class N P, cast_class P N}.
Context `{spec_of N nat, spec_of P pos}.

Global Instance zeroZ : zero Z := Zpos 0.
Global Instance oneZ : one Z := Zpos 1.

Global Instance addZ : add Z := fun x y : Z =>
match x, y with
| Zpos x, Zpos y => Zpos (x + y)
| Zneg x, Zneg y => Zneg (x + y)
| Zpos x, Zneg y => if (cast y <= x) then Zpos (x - cast y)
                      else Zneg (cast (cast y - x))
| Zneg x, Zpos y => if (cast x <= y) then Zpos (y - cast x)
                      else Zneg (cast (cast x - y))
end.

Global Instance oppZ : opp Z := fun x : Z =>
match x with
| Zpos x => if (x == 0)%C then 0%C else Zneg (cast x)
| Zneg x => Zpos (cast x)
end.

Global Instance subZ : sub Z := fun x y : Z =>
match x, y with
| Zpos x, Zneg y => Zpos (x + cast y)
| Zneg x, Zpos y => if (y == 0)%C then Zneg x else Zneg (x + cast y)
| Zpos x, Zpos y => if (y <= x) then Zpos (x - y)
                      else Zneg (cast (y - x))
| Zneg x, Zneg y => if (cast x <= cast y) then Zpos (cast y - cast x)
                      else Zneg (cast (cast x - cast y))
end.

Global Instance eqZ : eq Z := fun x y : Z =>
match x, y with
| Zpos x, Zpos y => (x == y)
| Zneg x, Zneg y => (x == y)
| _, _ => false
end.

Global Instance mulZ : mul Z := fun x y : Z =>
match x, y with
| Zpos x, Zpos y => Zpos (x * y)
| Zneg x, Zpos y => if (y == 0)%C then 0%C else Zneg (x * cast y)
| Zpos x, Zneg y => if (x == 0)%C then 0%C else Zneg (cast x * y)
| Zneg x, Zneg y => Zpos (cast x * cast y)
end.

Global Instance cast_NZ : cast_class N Z :=
  fun n : N => Zpos n.

Global Instance cast_PZ : cast_class P Z :=
  fun n : P => Zpos (cast n).

Global Instance specZ : spec_of Z int :=
  fun x => (match x with
             | Zpos p => (spec p)%:Z
             | Zneg n => - (val (spec n))%:Z
           end)%R.

End binint_op.

(******************************************************************************)
(** PART II: Proving correctness properties of the previously defined objects *)
(******************************************************************************)
Section binint_theory.

Notation Znp := (Z nat pos).

Definition Z_of_int (m : int) : Znp := match m with
  | Posz m => Zpos _ m
  | Negz m => Zneg _ (posS m)
  end.

Definition int_of_Z (m : Znp) : int := match m with
  | Zpos p => p%:Z
  | Zneg p => -(val p)%:Z
  end.

Lemma Z_of_intK : pcancel Z_of_int (some \o int_of_Z).
Proof. by rewrite /Z_of_int /int_of_Z => [[[]|]]. Qed.

Definition Rint : int -> Znp -> Prop := fun_hrel int_of_Z.

Import Op AlgOp.
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

Local Instance cast_pos_nat : cast_class pos nat := val.
Local Instance cast_nat_pos : cast_class nat pos := insubd 1%C.

Local Instance spec_nat : spec_of nat nat := spec_id.
Local Instance spec_pos : spec_of pos pos := spec_id.

(* Local Notation refines := refines_step. *)
Lemma RintE n x : param Rint n x -> n = int_of_Z x.
Proof. by rewrite paramE. Qed.

Local Instance refines_int_0 : param Rint (0%R : int) (0%C : Znp).
Proof. by rewrite paramE. Qed.
Local Instance refines_int_1 : param Rint (1%R : int) (1%C : Znp).
Proof. by rewrite paramE. Qed.

Local Instance refines_int_Posz :
  param (Logic.eq ==> Rint) Posz (cast : nat -> Znp).
Proof. by rewrite paramE=> n n' [<-]. Qed.

Local Instance refines_int_add :
  param (Rint ==> Rint ==> Rint) +%R +%C.
Proof.
rewrite paramE /Rint /fun_hrel /add_op /= => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; rewrite ?(add0r, addr0) //=; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [yx|xy] /= := leqP; first by rewrite addrC subzn.
  by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
by rewrite !insubdK -?topredE /= ?addn_gt0 ?valP // -opprB opprK addrC.
Qed.

Local Instance refines_int_opp : param (Rint ==> Rint) -%R -%C.
Proof.
rewrite paramE  /Rint /fun_hrel => _ x <-.
by case: x => [[]|] //= n; rewrite ?insubdK ?opprK.
Qed.

Local Instance refines_int_sub :
  param (Rint ==> Rint ==> Rint) subr sub_op.
Proof.
rewrite paramE  /Rint /fun_hrel /subr /sub_op => _ x <- _ y <-.
case: x y => [x|x] [y|y]; rewrite ?opprK //=; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [->|y_neq0 /=] := (altP eqP); first by rewrite subr0.
  by rewrite !insubdK -?opprD -?topredE //= ?addn_gt0 ?valP ?lt0n.
have [yx|xy] /= := leqP; first by rewrite addrC subzn.
by rewrite insubdK // -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
Qed.

Local Instance refines_int_eq :
  param (Rint ==> Rint ==> Logic.eq) eqtype.eq_op (@eq_op Znp _).
Proof.
rewrite paramE  /Rint /fun_hrel  /eq_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; rewrite ?eqr_opp // ?[- _ == _]eq_sym;
by rewrite gtr_eqF // (@ltr_le_trans _ 0) // ltr_oppl oppr0 [_ < _]valP.
Qed.

Local Instance refines_int_mul :
  param (Rint ==> Rint ==> Rint) *%R *%C.
Proof.
rewrite paramE  /Rint /fun_hrel  /mul_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; simpC; last by rewrite mulrNN.
  have [->|y_neq0 /=] := (altP eqP); first by rewrite mul0r.
  by rewrite mulrN !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
have [->|y_neq0 /=] := (altP eqP); first by rewrite mulr0.
by rewrite mulNr !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
Qed. 

Local Instance refines_specZ x : param Rint (spec x) x.
Proof. by rewrite !paramE; case: x. Qed.

Local Instance refines_specZ' :
  param (Rint ==> Logic.eq) id spec.
Proof. by rewrite paramE => a a' ra; rewrite [spec _]RintE. Qed.

(*************************************************************************)
(* PART III: Parametricity part                                          *)
(*************************************************************************)
Section binint_parametricity.

Section Zrefinement.
Variables N N' P P' : Type.
Variables (RN : N -> N' -> Prop) (RP : P -> P' -> Prop).

Local Notation Z' := (Z N' P').
Local Notation Z := (Z N P).

Definition RZ : Z -> Z' -> Prop :=
  fun x y => match x, y with 
                 Zpos x, Zpos y => RN x y
               | Zneg x, Zneg y => RP x y
               | _, _ => False end.

Lemma param_Zpos : (getparam RN ==> getparam RZ)%rel (@Zpos N P) (@Zpos N' P').
Proof. by rewrite !paramE. Qed.

Lemma param_Zneg : (getparam RP ==> getparam RZ)%rel (@Zneg N P) (@Zneg N' P').
Proof. by rewrite !paramE. Qed.

Lemma param_Zmatch T T' (R : T -> T' -> Prop) :
  (* interp_rel_type (RelBase RZ ==> (RelBase RN ==> RelBase R) ==> *)
  (*                          (RelBase RP ==> RelBase R) ==> RelBase R)%relt  *)
  (param RZ ==> getparam (RN ==> R) ==> getparam (RP ==> R) ==> getparam R)%rel 
  (@Zmatch _ _ _) (@Zmatch _ _ _).
Proof.
rewrite ?paramE => x x' rx f f' rf g g' rg.
by case: x x' rx=> [a|b] [a'|b'] //= rab; [apply: rf|apply: rg].
Qed.

End Zrefinement.

Arguments param_Zmatch {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments param_Zpos {_ _ _ _ _ _ _ _ _}.
Arguments param_Zneg {_ _ _ _ _ _ _} _ _.

Hint Extern 1 (getparam _ _ _) => eapply param_Zmatch: typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
eapply param_Zneg: typeclass_instances.
Hint Extern 1 (getparam _ _ _) =>
eapply param_Zpos: typeclass_instances.

Section binint_nat_pos.
Variables N P : Type.
Variables (Rnat : nat -> N -> Prop) (Rpos : pos -> P -> Prop).

Definition RZNP := (Rint \o RZ Rnat Rpos)%rel.

Import Op.
Context `{zero N, one N, sub N, add N, mul N, leq N, eq N}.
Context `{one P, sub P, add P, mul P, eq P}.
Context `{cast_class N P, cast_class P N}.
Context `{spec_of N nat, spec_of P pos}.

Context `{!param Rnat 0%N 0%C, !param Rnat 1%N 1%C}.
Context `{!param Rpos pos1 1%C}.
Context `{!param (Rnat ==> Rnat ==> Rnat) addn +%C}.
Context `{!param (Rpos ==> Rpos ==> Rpos) add_pos +%C}.
Context `{!param (Rnat ==> Rnat ==> Rnat) subn sub_op}.
Context `{!param (Rpos ==> Rpos ==> Rpos) sub_pos sub_op}.
Context `{!param (Rnat ==> Rnat ==> Rnat) muln *%C}.
Context `{!param (Rpos ==> Rpos ==> Rpos) mul_pos *%C}.
Context `{!param (Rnat ==> Rnat ==> Logic.eq) ssrnat.leq leq_op}.
Context `{!param (Rnat ==> Rpos) (insubd pos1) cast}.
Context `{!param (Rpos ==> Rnat) val cast}.
Context `{!param (Rnat ==> Rnat ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{!param (Rpos ==> Rpos ==> Logic.eq) eqtype.eq_op eq_op}.
Context `{forall x, param Rnat (spec x) x, 
          forall x, param Rpos (spec x) x}.
Context `{!param (Rnat ==> Logic.eq) spec_id spec, 
          !param (Rpos ==> Logic.eq) spec_id spec}.

Local Notation Z := (Z N P).

Global Instance param_zeroZ  : param RZNP (0 : int) (0%C : Z).
Proof. exact: param_trans. Qed.

Global Instance param_oneZ  : param RZNP (1 : int) (1%C : Z).
Proof. exact: param_trans. Qed.

Global Instance param_embedZ :
  param (Rnat ==> RZNP) (Posz : nat -> int) (cast : N -> Z).
Proof. exact: param_trans. Qed.

Global Instance param_addZ :
  param (RZNP ==> RZNP ==> RZNP) +%R +%C.
Proof. exact: param_trans. Qed.

Global Instance param_mulZ :
  param (RZNP ==> RZNP ==> RZNP) *%R *%C.
Proof. exact: param_trans. Qed.

Global Instance param_oppZ : param (RZNP ==> RZNP) -%R -%C.
Proof. exact: param_trans. Qed.

Global Instance param_subZ : param (RZNP ==> RZNP ==> RZNP) subr sub_op.
Proof. exact: param_trans. Qed.

Global Instance param_compZ :
  param (RZNP ==> RZNP ==> Logic.eq) eqtype.eq_op (@Op.eq_op Z _).
Proof. exact: param_trans. Qed.

Local Instance param_eq_refl A (x : A) : param Logic.eq x x | 999.
Proof. by rewrite paramE. Qed.
Local Instance param_fun_eq1 A B (f : A -> B) :
  param (Logic.eq ==> Logic.eq) f f.
Proof. by rewrite !paramE => x x' ->. Qed.
Local Instance param_fun_eq2 A B C (f : A -> B -> C) :
  param (Logic.eq ==> Logic.eq ==> Logic.eq) f f.
Proof. by rewrite !paramE => x x' -> y y' ->. Qed.

Global Instance param_specZ' :
  param (RZNP ==> Logic.eq) spec_id spec.
Proof. exact: param_trans. Qed.

End binint_nat_pos.
End binint_parametricity.
End binint_theory.
