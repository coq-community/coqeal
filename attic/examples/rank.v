(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset fingroup perm ssralg bigop matrix mxalgebra.
Require Import refinements.

Require Import ZArith ssrint hrel binint seqmatrix pivot rank boolF2.

Require binnat.

(*
Set Implicit Arguments.
*)

Open Scope ring_scope.

Definition M : 'M['F_2]_2 := 1%:M.

Definition N := \matrix_(i,j < 2) 2%num%:Z.
Definition P := \matrix_(i,j < 2) 14%num%:Z.

Import Refinements.

Instance : Op.zero nat := 0%N.
Instance : Op.one nat := 1%N.
Instance : Op.add nat := addn.

Instance : Op.zero 'F_2 := 0%R.
Instance : Op.inv 'F_2 := GRing.inv.
Instance : Op.eq 'F_2 := eq_op.
Instance : forall m n, Op.scale 'F_2 'M['F_2]_(m,n) :=
  fun m n => (@GRing.scale _ _).
Instance : Op.fun_of 'F_2 ordinal (matrix 'F_2) := (@fun_of_matrix 'F_2).

Instance : forall m, Op.zero (ordinal (1 + m)) := fun _ => 0%R.

Instance : Op.hadd (matrix 'F_2) := @addmx _.
Instance : Op.hsub (matrix 'F_2) := (fun _ _ M N => M - N).
Instance : Op.hmul (matrix 'F_2) := @mulmx _.
Instance : Op.lsub (matrix 'F_2) := @matrix.lsubmx 'F_2.
Instance : Op.rsub (matrix 'F_2) := @matrix.rsubmx 'F_2.
Instance : Op.block (matrix 'F_2) := @matrix.block_mx 'F_2.

Instance : Op.row_class ordinal (matrix 'F_2) := (@row 'F_2).
Instance : Op.row'_class ordinal (matrix 'F_2) := (@row' 'F_2).

Instance : forall m, Op.zero (ordinal m.+1) := fun _ => 0%R.
Instance : Op.lift0_class ordinal := fun _ => lift 0%R.
Instance : Op.dsub (matrix 'F_2) := fun _ _ _ => dsubmx.

Instance : Op.find_pivot_class 'F_2 ordinal (matrix 'F_2) :=
  find_pivot.

(* A helper instance to refine constant matrices *)
Instance param_const_fun {T U V W : Type} {R : T -> U -> Prop} {Q : V -> W -> Prop} {x a} `{!param Q x a} :
  param (R ==> Q) (fun _ => x) (fun _ => a).
Proof.
by rewrite paramE => ? ? ?; apply: paramR.
Qed.

(*
Instance param_eq_fun {T U V W : Type} {R : T -> U -> Prop} (f : V -> T) g `{!forall x, param R (f x) (g x)} :
  param (eq ==> R) f g.
Proof.
by rewrite paramE => ? ? ?; apply: paramR.
Qed.
*)

Set Typeclasses Debug.

(* Why does removing the 'F_2 annotation and tc instances above
   make tc inf loop? *)

Goal rank_elim _ _ _ _ 2 2 M = 2.
Proof.
apply/eqP.

erewrite param_eq; last first.
eapply param_apply.
eapply param_apply.
by tc.
eapply param_apply.

eapply (@RseqmxA_rank_elim _ _ bool Rbool).
eapply param_apply.
(* Why isn't this found by tc resolution? *)
eapply RseqmxA_scalarseqmx.
by tc.
by tc.
by tc.
(* At this point, unary numbers have disappeared. *)
by compute.
Qed.
