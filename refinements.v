(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop generic_quotient.
Require Import Morphisms.

(** This file implements the basic theory of refinements using operational
type classes and arbitrary arity morphism lemmas 

Implem A B  == B implements A, there is a function implem : A -> B 
Refines A B == B refines A, implem is injective 
Morph R f g == ?
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Reserved Notation "| f |" (at level 10, format "| f |"). *)
(* Reserved Notation "R \==> S" (at level 55, right associativity). *)

Delimit Scope computable_scope with C.
Delimit Scope signature_scope with S.

Local Open Scope ring_scope.

Import GRing.Theory.

Section Refinements. 

Class Implem A B := implem_op : A -> B.
Local Notation "|  x |" := (implem_op x) (at level 10) : computable_scope.
Class Refines {A B} `(Implem A B) := { inj_implem : injective implem_op }.

Section RefinesTheory.

Global Program Instance ImplemId {A} : Implem A A := id.
Global Program Instance ImplemTrans {A B C} `{Implem A B, Implem B C} : 
  Implem A C := implem_op \o implem_op.

Global Program Instance RefinesId {A} : Refines (@ImplemId A).
Obligation 1. by []. Qed.

Global Program Instance RefinesTrans {A B C} 
  `{H1 : Refines A B, H2 : Refines B C} : Refines ImplemTrans.
Obligation 1.
apply: inj_comp => //.
by case: H2.
Qed.

(* Refinements from quotients *)
Section Quotients.

Variable T : Type.
Variable qT : quotType T.

Local Open Scope quotient_scope.

(* It might make sense to use repr_of to avoid the lock on repr so that implem
   computes for quotients compute in the end. *)
(* Lemma repr_ofK : cancel (@repr_of _ qT) \pi_(qT). *)
(* Proof. by move: (@reprK _ qT); rewrite unlock. Qed. *)
(* Lemma inj_repr_of : injective (@repr_of _ qT). *)
(* Proof. exact: (can_inj repr_ofK). Qed. *)

Lemma inj_repr : injective (@repr _ qT).
Proof. exact: (can_inj (@reprK _ qT)). Qed.

(* Build implem and refines instances *)
Global Program Instance quot_implem : Implem qT T := @repr _ qT.
Global Program Instance quot_refines : Refines quot_implem.
Obligation 1. exact: inj_repr. Qed.

End Quotients.
End RefinesTheory.
End Refinements.

Notation "|  x |" := (implem_op x) (at level 10) : computable_scope.

(* Arbitrary arity morphisms a la Proper *)
Section Morphisms.

Local Open Scope computable_scope.

Class Morph {A B} (R : A -> B -> Prop) (m : A) (n : B) :=
  morph_prf : R m n.

(* Turn implem into a relation on A and B *)
Definition implem {A B} `{Implem A B} : A -> B -> Prop :=
  fun x y => | x | = y.

(* We can build relations on function spaces *)
Definition respectful_gen {A B C D : Type}
  (R : A -> B -> Prop) (R' : C -> D -> Prop) : (A -> C) -> (B -> D) -> Prop :=
  respectful_hetero _ _ _ _ R (fun x y => R').

Local Notation " R ==> S " := (@respectful_gen _ _ _ _ R S)
    (right associativity, at level 55) : signature_scope.

Section MorphTheory.

(* TODO: Need something more general to handle arbitrary operations! *)
Variables A B C : Type.
Context `{Implem A B, Implem B C,
          a : A, b : B, c : C,
          mAB : !Morph implem a b, mBC : !Morph implem b c}.

Global Program Instance MorphTrans : Morph implem a c.
Obligation 1.
move: mAB mBC.
by rewrite /Morph /ImplemTrans /implem /implem_op /= => -> ->.
Qed.

End MorphTheory.
End Morphisms. 

Notation " R ==> S " := (@respectful_gen _ _ _ _ R S)
    (right associativity, at level 55) : signature_scope.

Section Operations.

Local Open Scope signature_scope.

(* Zero arity operations, i.e. constants *)
Class Zero B := zero : B.
Local Notation "0" := zero : computable_scope.

Class One B := one_op : B.
Local Notation "1" := one_op : computable_scope.

(* Unary operations *)
Class Opp B := opp : B -> B.
Local Notation "- x" := (opp x) : computable_scope.

(* Binary operations *)
(* TODO: Fix binding prorities *)
Class Add B := add : B -> B -> B.
Local Notation "x + y" := (add x y) : computable_scope.
(* Notation "+%C" := add : computable_scope. *)

Class Sub B := sub : B -> B -> B.
Local Notation "x - y" := (sub x y) : computable_scope.

Class Mul B := mul : B -> B -> B.
Local Notation "x * y" := (mul x y) : computable_scope.

Class Div B := div : B -> B -> B.
Local Notation "x / y" := (div x y) : computable_scope.

(* Comparisons *)
Class Comp B := comp : B -> B -> bool.
Local Notation "x == y" := (comp x y) : computable_scope.

Section OperationsTheory.

(* This might be a nice lemma, anyway it shows how to write lemmas
   and that sharing of impl works *)
Lemma implem_eq0 (A : zmodType) B
  `{Comp B, Zero B, Implem A B,
    compE : !Morph (implem ==> implem ==> implem)
                   (fun x y => x == y) (fun x y => x == y)%C,
    zeroE : !Morph implem 0 0%C} a :
  (a == 0) = (| a | == 0)%C.
Proof.
by apply/eqP/idP => [->|]; rewrite -zeroE -compE // => /eqP ->.
Qed.

End OperationsTheory.
End Operations.

Notation "0"      := zero : computable_scope.
Notation "1"      := one_op : computable_scope.
Notation "- x"    := (opp x) : computable_scope.
Notation "x + y"  := (add x y) : computable_scope.
Notation "x - y"  := (sub x y) : computable_scope.
Notation "x * y"  := (mul x y) : computable_scope.
Notation "x / y"  := (div x y) : computable_scope.
Notation "x == y" := (comp x y) : computable_scope.