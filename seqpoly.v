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
Local Open Scope signature_scope.

Import GRing.Theory.

Section seqpoly.

Variable A : ringType.
Variable B : Type.

Definition seqpoly := seq B.

Global Program Instance ImplemSeqpoly `{Implem A B} : Implem {poly A} seqpoly := 
  map implem_op.
Global Program Instance RefinesSeqpoly `{Refines A B} : Refines ImplemSeqpoly.
Obligation 1.
move => x y h.
by apply/poly_inj/(inj_map _ h)/inj_implem.
Qed.

Global Program Instance ZeroSeqpoly : Zero seqpoly := [::].
Global Program Instance ZeroMorphSeqpoly `{Implem A B} : Morph implem 0 0%C.
Obligation 1. by rewrite /implem /implem_op /ImplemSeqpoly polyseq0. Qed.

Global Program Instance OneSeqpoly `{One B} : One seqpoly := [:: 1%C].
Global Program Instance OneMorphSeqpoly `{One B, Implem A B,
  oneE : !Morph implem 1 1%C} : Morph implem 1 1%C.

Fixpoint comp_seqpoly `{comp : Comp B} p q : bool := match p, q with
  | [::], [::] => true
  | x :: xs, y :: ys => comp x y && comp_seqpoly xs ys
  | _, _ => false
  end.

Global Program Instance CompSeqpoly `{Comp B} : Comp seqpoly := comp_seqpoly.
(* I guess compE is needed as well... *)
Global Program Instance CompMorphSeqpoly `{Comp B, Implem A B} :
  Morph (implem ==> implem ==> implem)
        (fun x y => x == y) (fun x y => x == y)%C.
Obligation 1. admit. Qed.

Fixpoint add_seqpoly `{Zero B, Add B, Comp B} p q : seqpoly := match p, q with
  | [::], _ => q
  | _, [::] => p
  | x :: xs, y :: ys =>
        let xy := (x + y)%C in
        let r  := add_seqpoly xs ys
        in if (xy == 0)%C then if comp_seqpoly r [::]
          then [::] else xy :: r else xy :: r
  end.

Global Program Instance AddSeqpoly `{Zero B, Add B, Comp B} : Add seqpoly :=
  add_seqpoly.
Global Program Instance AddMorphSeqpoly `{Refines A B, Zero B, Add B, Comp B} :
  Morph (implem ==> implem ==> implem) +%R (fun x y => x + y)%C.
Obligation 1.
rewrite /implem => a _ <- b _ <-.
admit.
Qed.

End seqpoly.

(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0 + 0)%C : seqpoly Z. *)
(* Eval compute in (1 + 1)%C : seqpoly Z. *)
(* Eval compute in 1%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1)%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1 + 1 + 1 + 1)%C :  *)
(*   seqpoly (seqpoly (seqpoly (seqpoly (seqpoly Z)))). *)