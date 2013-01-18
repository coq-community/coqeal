(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements.

(******************************************************************************)
(* Lists (seq) is a refinement of SSReflect polynomials (poly)                *) 
(*                                                                            *)
(* ImplemSeqpoly  == if B implements A then seqpoly B implements {poly A}     *)
(* RefinesSeqpoly == if B refines A then seqpoly B refines {poly A}           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.

Section seqpoly.

Variable A : ringType.

Definition seqpoly T := seq T.

Definition seqpoly_of_poly (p : {poly A}) : seqpoly A := polyseq p.
Definition poly_of_seqpoly (p : seqpoly A) : option {poly A} := Some (Poly p).

Lemma seqpoly_of_polyK : pcancel seqpoly_of_poly poly_of_seqpoly.
Proof. by rewrite /seqpoly_of_poly /poly_of_seqpoly /= => x; rewrite polyseqK. Qed.

Global Program Instance refinement_poly_seqpoly : refinement_of {poly A} (seqpoly A) := 
  Refinement seqpoly_of_polyK.

(* zero *)
Definition seqpoly_zero : seqpoly A := [::].
Global Program Instance zero_seqpoly : zero (seqpoly A) := seqpoly_zero.

Global Program Instance refines_poly_0 : refines 0 (0 : seqpoly A)%C.

(* one *)
Definition seqpoly_one : (seqpoly A) := [:: 1].
Global Program Instance one_seqpoly : one (seqpoly A) := seqpoly_one.

Global Program Instance refines_poly_1 : refines 1 1%C.
Obligation 1.
by congr Some; apply/poly_inj; rewrite polyseq1 polyseq_cons polyseq0 /= polyseq1.
Qed.

(* comp *)
(* Global Program Instance CompSeqpoly `{Comp B} : Comp seqpoly := comp_seqpoly. *)
(* (* I guess compE is needed as well... *) *)
(* Global Program Instance CompMorphSeqpoly `{Comp B, Implem A B} : *)
(*   Morph (implem ==> implem ==> implem) *)
(*         (fun x y => x == y) (fun x y => x == y)%C. *)
(* Obligation 1. admit. Qed. *)

(* THIS IS NOT TRUE! *)
(* Lemma refines_size (x : {poly A}) (a : seq A) (xa : refines x a) :  *)
(*   size x = size a. *)
(* Proof. *)
(* case: xa => /=; rewrite /seqpoly_pi /=. *)
(* move=> h. *)
(* move: (Some_inj h). *)
(* move<-. *)
(* f_equal. *)
(* admit. *)
(* Qed. *)

(* addition *)
(* THIS MIGHT BE WRONG! *)
Definition seqpoly_add (p q : seqpoly A) : seqpoly A := 
  \poly_(i < maxn (size p) (size q)) (p`_i + q`_i).

Global Program Instance add_seqpoly : add (seqpoly A) := seqpoly_add.

Global Program Instance refines_poly_add  (x y : {poly A}) (a b : seq A) 
  (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Obligation 1.
congr Some.
rewrite polyseqK.
rewrite [x + y]/GRing.add /= !unlock /=.
admit.
Qed.

End seqpoly.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0 + 0)%C : seqpoly Z. *)
(* Eval compute in (1 + 1)%C : seqpoly Z. *)
(* Eval compute in 1%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1)%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1 + 1 + 1 + 1)%C : *)
(*   seqpoly (seqpoly (seqpoly (seqpoly (seqpoly Z)))). *)