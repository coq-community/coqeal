(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp. 
Require Import path choice fintype tuple finset ssralg bigop ssrint ssrnum rat.
Require Import refinements.

(******************************************************************************)
(* Non-normalized rational numbers refinest SSReflects rational numbers (rat) *) 
(*                                                                            *)
(* rational == Type of non normalized rational numbers                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory.
Import Num.Theory.

(* rational - Non normalized rational numbers *)

Definition Q (B : Type) := (B * B)%type.
Local Notation Qint := (Q int).

(* Canonical Q_subType := Eval hnf in [subType for valr]. *)

(* Lemma val_inj : injective valr. *)
(* Proof. exact: val_inj. Qed. *)

(* rat_to_Qint = repr *) (* Qint_to_rat = \pi_rat *)
Definition rat_to_Qint (r : rat) : Qint := (numq r, denq r).
Definition Qint_to_rat (r : Qint) : option rat :=
  if r.2 != 0 then Some (r.1%:Q / r.2%:Q) else None.

Lemma Qrat_to_intK : pcancel rat_to_Qint Qint_to_rat.
Proof. by move=> x; rewrite /Qint_to_rat ?denq_eq0 ?divq_num_den. Qed.

(* We have a quotient type where rat is the quotients of Qint *)
(* IN FACT, THIS SHOULD BE A SUB-REFINEMENT, NOT A REFINEMENT!!! *)
Global Instance rat_refinement : refinement rat Qint :=
  Refinement Qrat_to_intK.

Lemma Qint2_eq0 (a : Qint) : (a.2 == 0) = ~~ spec a :> bool.
Proof. by rewrite /= /Qint_to_rat; case: (altP eqP). Qed.

(* this kind of things should be internalized in the theory of refinements *)
Lemma dom_refines (x : rat) (r : Qint) `{!refines x r} : r.2 != 0.
Proof. by rewrite Qint2_eq0 spec_refines. Qed.

Lemma refines_ratE (x : rat) (a : Qint) `{!refines x a} : x = a.1%:~R / a.2%:~R.
Proof. 
by apply: Some_inj; rewrite -spec_refines /= /Qint_to_rat dom_refines.
Qed.

Section Q.
Variable B : Type.
Context `{zero B, one B, add B, opp B, mul B, eq B}.
Local Notation ratB := (Q B).

(* Zero *)
Definition zeroQ : ratB := (0, 1)%C.
Global Instance zero_ratB : zero ratB := zeroQ.

(* One *)
Definition oneQ : ratB := (1, 1)%C.
Global Instance one_ratB : one ratB := oneQ.

(* Add *)
Definition addQ (x y : ratB) : ratB :=
   (x.1 * y.2 + y.1 * x.2, x.2 * y.2)%C.
Global Instance add_ratB : add ratB := addQ.

(* Mul *)
Definition mulQ (x y : ratB) : ratB := (x.1 * y.1, x.2 * y.2)%C.
Global Instance mul_ratB : mul ratB := mulQ.

(* Opp *)
Definition oppQ (x : ratB) : ratB := (- x.1, x.2)%C.
Global Instance opp_ratB : opp ratB := oppQ.

(* Comp *)
Definition eqQ (x y : ratB) : bool := (x.1 * y.2 == x.2 * y.1)%C.
Global Instance eq_ratB : eq ratB := eqQ.

(* Inv *)
Definition invQ (x : ratB) : ratB :=
  (if (x.1 == 0)%C then 0%C else (x.2, x.1)%C).
Global Instance inv_ratB : inv ratB := invQ.

(* Subtraction *)
Definition subQ (a b : ratB) : ratB := (a + - b)%C.
Global Instance sub_ratB : sub ratB := subQ.

(* Division *)
Definition divQ (a b : ratB) : ratB := (a * b^-1)%C.
Global Instance div_ratB : div ratB := divQ.

End Q.

Instance : zero int := 0%R.
Instance : one int  := 1%R.
Instance : add int  := +%R.
Instance : opp int  := -%R.
Instance : mul int  := *%R.
Instance : eq int   := eqtype.eq_op.


Instance refines_zeroq : refines_step 0 0%C. Proof. by []. Qed.
Instance refines_oneq : refines_step 1 1%C. Proof. by []. Qed.

Instance refines_addq (x y : rat) (a b : Qint)
         `{!refines_step x a, !refines_step y b} : refines_step (x + y) (a + b)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat mulf_neq0 ?dom_refines //=.
rewrite [x]refines_ratE [y]refines_ratE.
by rewrite addf_div ?intr_eq0 ?dom_refines ?(rmorphD, rmorphM).
Qed.

Instance refines_oppq (x : rat) (a : Qint) `{!refines_step x a} :
  refines_step (- x) (- a)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat /= ?dom_refines //=.
by rewrite [x]refines_ratE rmorphN mulNr.
Qed.

Instance refines_mulq (x y : rat) (a b : Qint)
         `{!refines_step x a, !refines_step y b} : refines_step (x * y) (a * b)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat mulf_neq0 ?dom_refines //=.
rewrite [x]refines_ratE [y]refines_ratE.
by rewrite mulrACA -invfM ?(rmorphD, rmorphM).
Qed.

Instance refines_invq (x : rat) (a : Qint) `{!refines_step x a} :
  refines_step (x^-1) (a^-1)%C.
Proof.
rewrite /refines_step /= /Qint_to_rat /= /inv_op /inv_ratB /invQ.
rewrite [x]refines_ratE /= -[(_ == _)%C]/(_ == _).
have [-> /=|a1_neq0 /=] := altP (a.1 =P 0); first by rewrite !mul0r ?invr0.
by rewrite a1_neq0 invfM invrK mulrC.
Qed.

Instance refines_subq (x y : rat) (a b : Qint)
 `{!refines_step x a, !refines_step y b} : refines_step (x - y) (a - b)%C.
Proof. by rewrite /refines_step spec_refines. Qed.

Instance refines_divq (x y : rat) (a b : Qint)
 `{!refines_step x a, !refines_step y b} : refines_step (x / y) (a / b)%C.
Proof. by rewrite /refines_step spec_refines. Qed.

Instance refines_compq (x y : rat) (a b : Qint)
 `{!refines_step x a, !refines_step y b} : refines_step (x == y) (a == b)%C.
Proof.
congr Some; rewrite /= /eq_op /eq_ratB /eqQ. 
rewrite [x]refines_ratE [y]refines_ratE /= -[(_ == _)%C]/(_ == _).
rewrite divq_eq ?intr_eq0 ?dom_refines // -!rmorphM eqr_int.
by rewrite [X in (_ == X)]mulrC.
Qed.

Section Qparametric.

Import parametric_pair.

Global Instance Qrefinement_int B `{refinement int B} :
  refinement rat (Q B) :=  @refinement_trans _ Qint _ _ _.

Global Instance rat_refines_trans
         B `{refinement int B} (x : rat) (a : Qint) (u : Q B) :
         refines_step x a -> refines a u -> refines x u.
Proof. move=> /refines_step_refines; exact: @refines_trans. Qed.

(* B is a type that should implement int *)
Variable (B : Type).
Local Notation ratB := (Q B).

(* Build a context with proper sharing and the necessary refinements *)
(* this should be done by refinesiy *)
Context `{zero B, one B, add B, opp B, mul B, eq B}.
Context `{refinement int B}.

Context `{!refines (0%C : int) (0%C : B)}
        `{!refines (1%C : int) (1%C : B)}
        `{forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x + y)%C (a + b)%C}
        `{forall (x : int) (a : B) `{!refines x a},
            refines (- x)%C (- a)%C}
        `{forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x * y)%C (a * b)%C}
        `{forall (x y : int) (a b : B) `{!refines x a, !refines y b},
            refines (x == y)%C (a == b)%C}.

Global Instance refines_zeroQ : refines (0%C : Q int) (0%C : Q B).
Proof. by typeclasses eauto. Qed.

Global Instance refines_oneQ : refines (1%C : Q int) (1%C : Q B).
Proof. by typeclasses eauto. Qed.

Global Instance refines_addQ (x y : Q int) (a b : Q B)
         `{!refines x a, !refines y b} : refines (x + y)%C (a + b)%C.
Proof. by typeclasses eauto. Qed.

Global Instance refines_compQ (x y : Q int) (a b : Q B)
         `{!refines x a, !refines y b} : refines (x == y)%C (a == b)%C.
Proof. by typeclasses eauto. Qed.

End Qparametric.

(* Instance foo : refines_step (x + y) (a + b)%C. *)
(* Proof. typeclasses eauto. Qed. *)


Section tests.

(* Variable (B : Type). *)
(* Local Notation ratB := (Q B). *)

(* (* Build a context with proper sharing and the necessary refinements *) *)
(* (* this should be done by refinesiy *) *)
(* Context `{zero B, one B, add B, opp B, mul B, eq B}. *)
(* Context `{refinement int B}. *)

(* Context `{!refines (0%C : int) (0%C : B)} *)
(*         `{!refines (1%C : int) (1%C : B)} *)
(*         `{forall (x y : int) (a b : B) `{!refines x a, !refines y b}, *)
(*             refines (x + y)%C (a + b)%C} *)
(*         `{forall (x : int) (a : B) `{!refines x a}, *)
(*             refines (- x)%C (- a)%C} *)
(*         `{forall (x y : int) (a b : B) `{!refines x a, !refines y b}, *)
(*             refines (x * y)%C (a * b)%C} *)
(*         `{forall (x y : int) (a b : B) `{!refines x a, !refines y b}, *)
(*             refines (x == y)%C (a == b)%C}. *)

(* Lemma foo (P : bool -> Type) : *)
(*   P (1 + 1 == 0 + 1 + 1 :> rat). *)


(* refine (let x : refines (1 + 1 == 0 + 1 + 1 :> rat) _ := _ in _). *)
(* assert (t := @bool_refines (1 + 1 == 0 + 1 + 1 :> rat) _ _). *)

(* rewrite [_ == _]bool_refines. *)


(* Lemma foo (P : bool -> Type)  (x y : rat) (u v : Qint) (a b : Q B) *)
(*          `{!refines x a, !refines y b}  *)
(*          (* `{!refines u a, !refines v b}  *) : P (a + b == b + a)%C.  *)
(* Proof. typeclasses eauto. *)
(* assert (t := @bool_refines _ (a + b == b + a)%C _). *)



(* TODO: 
     - normq
     - le_rat
     - lt_rat
*)

(*
Require Import ZArith ssrint binint.

Eval compute in (0%C + 0%C + 0%C)%C : Z * Z.
*)

(*
Lemma bool_implem P (b : bool) : P (\implem_bool b)%C -> P b.
Proof. done. Qed.
*)


(* Goal (2500%:Q = 2500%:Q). *)
(* Proof. *)
(* apply/eqP. *)
(* Check (refines_rat_comp _ _ _ _ (intr_refines (Posz 2500)) *)
(* (intr_refines (Posz 2500))). *)


(* rewrite [_ == _](@bool_refine _ _ (refines_rat_comp _ _ _ _ (intr_refines (Posz 2500)) *)
(* (intr_refines (Posz 2500)))). *)

(* (* missing refinement for intr and default refinement for naturals *) *)
(* Qed. *)

(* Goal (1000%:Q + 1500%:Q = 2500%:Q). *)
(* Proof. *)
(* apply/eqP. *)
(* rewrite [_ == _](bool_refine refines_rat_comp). *)
(* (* missing refinement for intr and default refinement for naturals *) *)
(* Qed. *)
(* *)

End tests.


(* Section old_parametricity. *)
(* For backup *)

(* Class relation (T T' : Type) : Type := trel : T -> T' -> Type. *)

(* Instance relation_forall (F : Type -> Type) (F' : Type -> Type) *)
(*   (RF : forall X X' : Type, relation X X' -> relation (F X) (F' X')) : *)
(*    relation (forall X, F X) (forall X, F' X) := *)
(* (fun g g' => forall (X X' : Type) (R : X -> X' -> Type), RF _ _ R (g X) (g' X')). *)

(* Instance relation_fun  (A A' : Type) (B : A -> Type) (B' : A' -> Type) *)
(*        (RA : relation A A') (RB : forall x x', relation (B x) (B' x')) : *)
(*   relation (forall x, B x) (forall x', B' x') := *)
(* (fun f f' => forall x x' (RAxx' : RA x x'), RB _ _ (f x) (f' x')). *)

(* Instance relation_pair  (A A' : Type) (B : Type) (B' : Type) *)
(*   (RA : relation A A') (RB : relation B B') : relation (A * B) (A' * B') := *)
(* (fun ab ab' => RA ab.1 ab'.1 * RB ab.2 ab'.2)%type. *)

(* Class parametric {T T' : Type} {R : relation T T'} t1 t2 := *)
(*   parametricity : R t1 t2. *)

(* Instance apply_parametric *)
(*         (A A' : Type) (B : A -> Type) (B' : A' -> Type) *)
(*         (f : forall x : A, B x) (f' : forall x' : A', B' x') *)
(*         (RA : relation A A') (RB : forall x x', relation (B x) (B' x')) *)
(*         (x : A) (x' : A') (px : parametric x x') *)
(*         (pf : parametric f f') : parametric (f x) (f' x'). *)
(* Proof. by have :=  pf _ _ px. Qed. *)

(* Instance parametric_pair (A A' B B' : Type) *)
(*         (a : A) (a' : A') (b : B) (b' : B') *)
(*         (RA : relation A A') (RB : relation B B') : *)
(*   parametric a a' -> parametric b b' -> *)
(*   parametric  (a, b) (a', b'). *)
(* Proof. by constructor. Qed. *)

(* Instance parametric_fst (A A' B B' : Type) *)
(*         (RA : relation A A') (RB : relation B B') *)
(*         (ab : A * B) (ab' : A' * B') : *)
(*   parametric ab ab' -> parametric ab.1 ab'.1. *)
(* Proof. by case. Qed. *)

(* Instance parametric_snd (A A' B B' : Type) *)
(*         (RA : relation A A') (RB : relation B B') *)
(*         (ab : A * B) (ab' : A' * B') : *)
(*   parametric ab ab' -> parametric ab.2 ab'.2. *)
(* Proof. by case. Qed. *)

(* Instance relation_refines (A B : Type) `{refinement A B} : *)
(*   relation A B := fun x a => refines x a. *)

(* Global Instance refines_parametric (A B : Type) *)
(*          `{refinement A B} (a : A) (b : B) : *)
(*   refines a b -> parametric a b. *)
(* Proof. done. Qed. *)

(* Definition rat_parametric_refines (A B : Type) `{refinement A B} *)
(*   (a : Q A) (b : Q B) : parametric a b -> \refines_Qrefinement a b. *)
(* Proof. *)
(* case: a b => [x y] [z t] /=; rewrite /QBtoA /refines /=. *)
(* by case; rewrite /relation_refines => /= ra1 ra2; rewrite !spec_refines. *)
(* Qed. *)

(* Global Instance rat_refines_parametric_trans *)
(*          B `{refinement int B} (x : rat) (a : Qint) (u : Q B) *)
(*          (rx : refines x a) : parametric a u -> refines x u. *)
(* Proof. by move=> /rat_parametric_refines; apply: @rat_refines_trans. Qed. *)

(* End old_parametricity. *)
