(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset fingroup perm ssralg bigop matrix mxalgebra.
Require Import refinements.

Require Import ZArith ssrint hrel binint seqmatrix.

Require binnat.

(*
Set Implicit Arguments.
*)

Open Scope ring_scope.

Definition M := \matrix_(i,j < 2) 1%num%:Z.
Definition N := \matrix_(i,j < 2) 2%num%:Z.
Definition P := \matrix_(i,j < 2) 14%num%:Z.

(* A first failed attempt *)
Goal - P = - P.
Proof.
apply/eqP.
erewrite param_eq; last first.
eapply param_apply.
eapply param_apply.

(* Why does Coq pick the instance binnat.eq_N for the argument H of the
following lemma? *)
eapply RseqmxA_eqseqmx.
Fail by tc.
Abort.

(* A helper instance to refine constant matrices *)
Instance param_fun {T U V W : Type} {R : T -> U -> Prop} {Q : V -> W -> Prop} {x a} `{!param Q x a} :
  param (R ==> Q) (fun _ => x) (fun _ => a).
Proof.
by rewrite paramE => ? ? ?; apply: paramR.
Qed.

Set Typeclasses Debug.

(* A sucessful attempt *)
Goal - P = - P.
Proof.
apply/eqP.
rewrite [_ == _]param_eq.
(* At this point, unary numbers have disappeared. *)
by compute.
Qed.

Goal (M + N + M + N + M + N + N + M + N) *m
   (M + N + M + N + M + N + N + M + N) = 
(P *m M + P *m N + P *m M + P *m N + 
 P *m M + P *m N + P *m N + P *m M + P *m N).
Proof.
apply/eqP.
rewrite [_ == _]param_eq.
by compute.
Qed.

(* Let's try with non-constant matrices, defined by lists *)
Definition Qseq := [:: [:: 4%num%:Z; 2%num%:Z; 2%num%:Z]; [:: 2%num%:Z; 8%num%:Z; 2%num%:Z]].
Definition Q := \matrix_(i < 2, j < 3) nth 0 (nth [::] Qseq i) j.

(*
Definition Q := @mx_of_seqmx_val int 0 2 3 Qseq.
*)

Goal - Q = - Q.
Proof.
rewrite /Q /Qseq.
apply/eqP.
erewrite param_eq; last first.
eapply param_apply.
eapply param_apply.
by tc.
eapply param_apply.
by tc.
eapply param_apply.
eapply RseqmxA_mkseqmx_mx_key.

eapply get_param. (* This is needed to synthetize the list *)
eapply getparam_abstr => ? ? ?.
eapply getparam_abstr => ? ? ?.
eapply getparam_nth.
by tc.
eapply getparam_nth.
by tc.
by tc.


by tc.
eapply param_apply.
by tc.
eapply param_apply.
by tc.
eapply get_param.
by tc.
(* At this point, unary numbers have disappeared. *)
by compute.
Qed.