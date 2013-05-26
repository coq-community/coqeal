(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements binnat.

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

Notation pos := {n : nat | (n > 0)%N}.

(* Programming part *)
Section Zdef.
Variable N P : Type.
Inductive Z := Zpos of N | Zneg of P.

Definition Zmatch T (n : Z) f g : T := match n with Zpos p => f p | Zneg n => g n end.
Definition Zmatch2 T (m n : Z) fpp fnn fpn fnp : T :=
  Zmatch m (fun x => Zmatch n (fpp x) (fpn x)) (fun x => Zmatch n (fnp x) (fnn x)).

Local Open Scope computable_scope.
Import Op AlgOp.

Context `{zero N, one N, sub N, add N, mul N, leq N, eq N}.
Context `{one P, sub P, add P, mul P, eq P}.
Context `{cast_class N P, cast_class P N}.

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

Global Instance cast_P_Z : cast_class P Z :=
  fun n : P => Zpos (cast n).

End Zdef.

(* Proof part, should be refactored *)
Section Z_nat_pos.

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

Definition Rint : int -> Z -> Prop := fun_hrel int_of_Z.

Global Program Instance refinement_int_Z : refinement Rint := Refinement Z_of_intK _.
Next Obligation. by split=> [??[<-]|??<-]. Qed.

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
 
(* Local Notation refines := refines_step. *)
Lemma refines_intE n x : refines n x -> n = int_of_Z x.
Proof. by case. Qed.

Global Instance refines_int_0 : param refines (0%R : int) (0%C : Z).
Proof. by rewrite paramE. Qed.
Global Instance refines_int_1 : param refines (1%R : int) (1%C : Z).
Proof. by rewrite paramE. Qed.

Global Instance refines_int_Posz :
  param (Logic.eq ==> refines) Posz (cast : nat -> Z).
Proof. by rewrite paramE=> n n' [<-]. Qed.

Global Instance refines_int_add :
  param (refines ==> refines ==> refines) +%R +%C.
Proof.
apply param_abstr2 => _ x <- _ y <-.
rewrite /refines paramE /Rint /fun_hrel /add_op /=.
case: x y => [x|x] [y|y] //=; rewrite ?(add0r, addr0) //=; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [yx|xy] /= := leqP; first by rewrite addrC subzn.
  by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
by rewrite !insubdK -?topredE /= ?addn_gt0 ?valP // -opprB opprK addrC.
Qed. 

Global Instance refines_int_opp : param (refines ==> refines) -%R -%C.
Proof.
rewrite paramE /refines /Rint /fun_hrel => _ x <-.
by case: x => [[]|] //= n; rewrite ?insubdK ?opprK.
Qed.

Global Instance refines_int_sub :
  param (refines ==> refines ==> refines) subr sub_op.
Proof.
rewrite paramE /refines /Rint /fun_hrel /subr /sub_op => _ x <- _ y <-.
case: x y => [x|x] [y|y]; rewrite ?opprK //=; simpC.
    have [yx|xy] /= := leqP; first by rewrite subzn.
    by rewrite insubdK -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprB.
  have [->|y_neq0 /=] := (altP eqP); first by rewrite subr0.
  by rewrite !insubdK -?opprD -?topredE //= ?addn_gt0 ?valP ?lt0n.
have [yx|xy] /= := leqP; first by rewrite addrC subzn.
by rewrite insubdK // -?topredE /= ?subn_gt0 // -subzn 1?ltnW // opprD opprK.
Qed.

Global Instance refines_int_eq :
  param (refines ==> refines ==> refines) eqtype.eq_op (@eq_op Z _).
Proof.
rewrite paramE /refines /Rint /fun_hrel  /eq_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; rewrite ?eqr_opp // ?[- _ == _]eq_sym;
by rewrite gtr_eqF // (@ltr_le_trans _ 0) // ltr_oppl oppr0 [_ < _]valP.
Qed.

Global Instance refines_int_mul :
  param (refines ==> refines ==> refines) *%R *%C.
Proof.
rewrite paramE /refines /Rint /fun_hrel  /mul_op => _ x <- _ y <-.
case: x y => [x|x] [y|y] //=; simpC; last by rewrite mulrNN.
  have [->|y_neq0 /=] := (altP eqP); first by rewrite mul0r.
  by rewrite mulrN !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
have [->|y_neq0 /=] := (altP eqP); first by rewrite mulr0.
by rewrite mulNr !insubdK -?topredE /= ?muln_gt0 ?valP ?andbT ?lt0n.
Qed. 

End Z_nat_pos.

(************************************************************************)
(* The presentation of what follows must be changed drastically:        *)
(*                                                                      *)
(* Indeed, refinementZ should not be presented as a refinement anymore, *)
(* but rather as the relation RZ which happens to be the sum relation   *)
(* between RNN' and RPP', and which  satisfies:                         *)
(* refines int (Z N P) \o RZ <=> refines int (Z N' P')                  *)
(************************************************************************)


(* Section Zparametric. *)

(* Section Zrefinement. *)
(* Variables N N' P P' : Type. *)
(* Context `{refinement N N'} `{refinement P P'}.  *)

(* Definition implem_ZNpos (x : Z N P) : (Z N' P') := *)
(*     match x with Zpos n => Zpos _ (implem n) | Zneg n => Zneg _ (implem n) end. *)
(* Definition spec_ZNpos (x : Z N' P') : option (Z N P) := *)
(*     match x with Zpos n => omap (@Zpos _ _) (spec n) | Zneg n => omap (@Zneg _ _) (spec n) end. *)
(* Lemma implem_ZNposK : pcancel implem_ZNpos spec_ZNpos. *)
(* Proof. by case => //= n; rewrite !implemK. Qed. *)

(* Local Instance refinementZ : refinement (Z N P) (Z N' P') := *)
(*   Refinement implem_ZNposK. *)

(* Global Instance param_Zpos : *)
(*    param (refines ==> refines) (@Zpos N P) (@Zpos N' P'). *)
(* Proof. by rewrite paramE=> x x' rx /=; rewrite /refines /= spec_refines. Qed. *)

(* Global Instance param_Zneg : *)
(*    param (refines ==> refines) (@Zneg N P) (@Zneg N' P'). *)
(* Proof. by rewrite paramE=> x x' rx /=; rewrite /refines /= spec_refines. Qed. *)

(* Lemma param_Zmatch T T' (R : T -> T' -> Prop) :  *)
(*        (param refines ==> getparam (refines ==> R) ==> getparam (refines ==> R) ==> param R) *)
(*        (fun n f g => match n with Zpos p => f p | Zneg n => g n end) *)
(*        (fun n f g => match n with Zpos p => f p | Zneg n => g n end). *)
(* Proof. *)
(* rewrite !paramE. *)
(* move=> n n' rn f f' rf g g' rg. *)
(* case: n n' rn=> [n|p] [n'|p'] //=; rewrite /refines //=; *)
(*   do ? by case: spec. *)
(*   by case hn': spec => [a|] //= [] [->]; apply rf. *)
(* by case hn': spec => [a|] //= [] [->]; apply rg. *)
(* Qed. *)


(* End Zrefinement. *)

(* Hint Extern 0 (param _ _ _) => *)
(*  eapply param_Zmatch : typeclass_instances. *)

(* Hint Extern 1 (@refinement (@Z _ _) _) => *)
(*   apply refinementZ : typeclass_instances. *)

(* Hint Extern 1 (@refinement _ (@Z _ _)) => *)
(*   apply refinementZ : typeclass_instances. *)

(* (* Existing Instances refines_split1 refines_split2. *) *)

(* (* Hint Extern 0 (param _ (@addZ _ _) (@addZ _ _)) *) *)
(* (*  => eapply param_addZ : typeclass_instances. *) *)

(* Definition ZNP := Z N positive. *)

(* Global Instance Zrefinement_N_pos : *)
(*   refinement int ZNP :=  @refinement_trans _ (Z nat pos) _ _ _. *)

(* (* Hint Extern 4 (composable _ _ (_ ==> _)) *) *)
(* (*  => eapply composable_imply_id2 : typeclass_instances. *) *)

(* (* Hint Extern 1 (composable _ _ _) *) *)
(* (*  => eapply imply_composable : typeclass_instances. *) *)

(* (* Z is a type that should implement int *) *)
(* (* Variable (Z : Type). *) *)

(* Local Notation Z := ZNP. *)

(* Global Instance refines_zeroZ  : param refines (0 : int) (0%C : Z). *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance refines_oneZ  : param refines (1 : int) (1%C : Z). *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance refines_embedZ : *)
(*   param (refines ==> refines) (Posz : nat -> int) (cast : N -> Z). *)
(* Proof. exact: param_trans. Qed.   *)

(* Global Instance refines_addZ : *)
(*   param (refines ==> refines ==> refines) +%R +%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance refines_mulZ : *)
(*   param (refines ==> refines ==> refines) *%R *%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance refines_oppZ : *)
(*   param (refines ==> refines) -%R -%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance refines_subZ : *)
(*   param (refines ==> refines ==> refines) AlgOp.subr Op.sub_op. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance refines_compZ : *)
(*   param (refines ==> refines ==> refines) eqtype.eq_op (@Op.eq_op Z _). *)
(* Proof. exact: param_trans. Qed. *)

(* End Zparametric. *)
