(** This example file is drawn from a Coq proof of irrationality of zeta(3) *)
(** which uses CoqEAL. *)
(** (c) Copyright INRIA and University of Gothenburg *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div choice.
Require Import ssralg ssrnum ssrint intdiv rat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArith.
Require Import CoqEAL.refinements.
Require Import CoqEAL.pos CoqEAL.binnat CoqEAL.binint CoqEAL.rational.
Import Refinements AlgOp.

Import GRing.Theory.
Import Num.Theory.

Open Scope ring_scope.

(* You don't really need Z here but positive *)
Definition rat_of_positive_fun (p : positive) : rat :=
  (pos_to_int (Op.spec p))%:~R.

Definition rat_of_positive_ := nosimpl rat_of_positive_fun.

Module Type RatOfZSig.
Parameter rat_of_positive : positive -> rat.
Axiom rat_of_positiveEdef : rat_of_positive = rat_of_positive_.
End RatOfZSig.

Module rat_of_positiveDef : RatOfZSig.
Definition rat_of_positive : positive -> rat := rat_of_positive_fun.
Definition rat_of_positiveEdef := erefl rat_of_positive.
End rat_of_positiveDef.

Export rat_of_positiveDef.

(* Generic programming of your functions : *)
(* we abstract wrt Q and all the operations you use *)
Section generic.
Import Refinements.
Import Op.

(* In the future, many of these might come packaged together *)
Context (AQ : Type).
Context (zeroAQ : zero AQ).
Context (addAQ : add AQ) (oppAQ : opp AQ) (subAQ : sub AQ).
Context (divAQ : div AQ) (mulAQ : mul AQ) (expAQ : exp AQ nat).
Context (positive_toAQ : cast_class positive AQ).
Context (nat_to_AQ : cast_class nat AQ).

Open Local Scope computable_scope.

Definition beta' (i : AQ) : AQ := 
  ((i + cast 1%positive) / (i + cast 2%positive)) ^ 3.

Definition alpha' (i : AQ) : AQ :=
     (cast 17%positive * i ^ 2 + cast 51%positive * i + cast 39%positive)
   * (cast 2%positive * i + cast 3%positive) / (i + cast 2%positive) ^ 3.

Definition h' (i : AQ) (x : AQ) := alpha' i  - beta' i / x.

Fixpoint h_iter' (n : nat) : AQ := 
  match n with
    | 0 => cast 0%C
    | 1 => cast 0%C
    | 2 => cast 1445%positive / cast 73%positive
    | m.+1 => let mz := cast m in
              let res_m := h_iter' m in
              h' mz res_m
  end.

End generic.

(* This is the "free" part of the refinements: *)
(* Parametricity of the previously operations.  For now our library
   provides a semi-automated resolution based on typeclasses. We aim
   to replace it by an ML plugin in Chantal Keller and Marc Lasson
   style so that it is as "free" in the implementation as it is in
   theory. *)
Section parametric.
Import Refinements.
Import Op.

Context (AQ : Type).
Context (zeroAQ : zero AQ) (addAQ : add AQ) (oppAQ : opp AQ) (subAQ : sub AQ).
Context (divAQ : div AQ) (mulAQ : mul AQ) (expAQ : exp AQ nat).
Context (ZtoAQ : cast_class positive AQ) (nat_to_AQ : cast_class nat AQ).
Context (RAQ : rat -> AQ -> Prop).
Context (RzeroAQ : param RAQ 0%R zero_op).
Context (RaddAQ : param (RAQ ==> RAQ ==> RAQ) +%R add_op).
Context (RoppAQ : param (RAQ ==> RAQ) -%R opp_op).
Context (RsubAQ : param (RAQ ==> RAQ ==> RAQ) subr sub_op).
Context (RmulAQ : param (RAQ ==> RAQ ==> RAQ) *%R mul_op).
Context (RdivAQ : param (RAQ ==> RAQ ==> RAQ) divr div_op).
Context (RexpAQ : param (RAQ ==> Logic.eq ==> RAQ) (@GRing.exp _) exp_op).
Context (RZtoAQ : param (Logic.eq ==> RAQ) rat_of_positive cast).
Context (Rnat_to_AQ : param (Logic.eq ==> RAQ) (intr : nat -> _) cast).

Local Instance eq_param T (x : T) : param Logic.eq x x.
Proof. by rewrite paramE. Qed.

Global Instance param_beta :
  param (RAQ ==> RAQ) (beta' +%R divr (@GRing.exp _) rat_of_positive) (beta' _ _ _ _).
Proof. by rewrite /beta'; apply: get_param. Qed.

Global Instance param_alpha :
  param (RAQ ==> RAQ) (alpha' +%R divr *%R (@GRing.exp _) rat_of_positive)
                      (alpha' _ _ _ _ _).
Proof. by rewrite /alpha'; apply: get_param. Qed.

Global Instance param_h :
  param (RAQ ==> RAQ ==> RAQ) 
    (h' +%R subr divr *%R (@GRing.exp _) rat_of_positive)
    (h' _ _ _ _ _ _).
Proof. by rewrite /h'; apply: get_param. Qed.

(* This is where a parametricity plugin would be useful *)
Global Instance param_h_iter n :
  param RAQ
    (h_iter' 0%R +%R subr divr *%R (@GRing.exp _) rat_of_positive intr n)
    (h_iter' _ _ _ _ _ _ _ _ n).
Proof.
elim: n => [|n ihn] //=; tc.
rewrite [h_iter']lock; case: n ihn => [|[|n]] ihn //=; tc.
by eapply param_apply; tc; rewrite -lock; apply: ihn.
Qed.

End parametric.

Section result.

Notation Q  := (Q (Z N positive) positive).
Notation RQ := (RratA (RZNP Rnat Rpos) Rpos).

(* A few things to get the compatibility between
   the CoqEAL library and your local requirements *)
Section extra_refinements.
Global Instance Q_of_nat : Op.cast_class nat Q :=
  fun n => iter n (Op.add_op 1%C) 0%C.

Global Instance RQ_of_nat : param (eq ==> RQ) (fun n : nat => n%:~R) cast.
Proof.
eapply param_abstr => n b; rewrite paramE => <- {b}.
rewrite /cast /Q_of_nat /= -[_%:~R]/n%:R.
elim: n => [|n ihn] //=; first by rewrite mulr0n; tc.
by rewrite mulrS; tc.
Qed.

Global Instance RQ_of_pos :
  param (Logic.eq ==> RQ) rat_of_positive cast.
Proof.
eapply param_abstr => n b; rewrite paramE => <- {b}.
rewrite rat_of_positiveEdef /rat_of_positive_ /rat_of_positive_fun.
by rewrite /cast /cast_PQ; tc.
Qed.

Global Instance positive_param_eq (x : positive) : param Logic.eq x x.
Proof. by rewrite paramE. Qed.
End extra_refinements.

(* Here is (almost) your h_iter function *)
Definition h_iter :=
  @h_iter' rat 0%R +%R subr divr *%R (@GRing.exp _) rat_of_positive intr.

(* And the answer is: *)
Lemma lt_33_r51 : h_iter 51 > rat_of_positive 33.
Proof. by rewrite [_ < _]param_eq; vm_compute. Qed.

End result.
