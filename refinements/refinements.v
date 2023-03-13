From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
(* Require Import path choice fintype tuple finset ssralg bigop poly polydiv. *)
(* Require Import ssrint ZArith. *)

From CoqEAL Require Import hrel param.

Require Import ssrmatching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic. *)
Declare Scope computable_scope.
Delimit Scope computable_scope with C.
Local Open Scope rel.

(* Shortcut for triggering typeclass resolution *)
Ltac tc := do 1?typeclasses eauto.

Section refinements.

Fact refines_key : unit. Proof. done. Qed.
Class refines A B (R : A -> B -> Type) (m : A) (n : B) :=
  refines_rel : (locked_with refines_key R) m n.
Arguments refines A B R%rel m n.

Lemma refinesE A B (R : A -> B -> Type) : refines R = R.
Proof. by rewrite /refines unlock. Qed.

Lemma refines_eq T (x y : T) : refines eq x y -> x = y.
Proof. by rewrite refinesE. Qed.

Global Instance refines_bool_eq x y : refines bool_R x y -> refines eq x y.
Proof. by rewrite !refinesE=> [[]]. Qed.

Lemma nat_R_eq x y : nat_R x y -> x = y.
Proof. by elim=> // m n _ ->. Qed.

Global Instance refines_nat_eq x y : refines nat_R x y -> refines eq x y.
Proof. rewrite !refinesE; exact: nat_R_eq. Qed.

Lemma refinesP T T' (R : T -> T' -> Type) (x : T) (y : T') :
  refines R x y -> R x y.
Proof. by rewrite refinesE. Qed.

Fact composable_lock : unit. Proof. done. Qed.
Class composable A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :=
  Composable : locked_with composable_lock (rAB \o rBC <= rAC).
Arguments composable A B C rAB%rel rBC%rel rAC%rel.

Lemma composableE A B C
 (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :
  composable rAB rBC rAC = (rAB \o rBC <= rAC).
Proof. by rewrite /composable unlock. Qed.

Lemma refines_trans A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type)
  (a : A) (b : B) (c : C) : composable rAB rBC rAC ->
  refines rAB a b -> refines rBC b c -> refines rAC a c.
Proof.
by rewrite !refinesE composableE => rABC rab rbc; apply: rABC; exists b.
Qed.

Lemma trivial_refines T T' (R : T -> T' -> Type) (x : T) (y : T') :
  R x y -> refines R x y.
Proof. by rewrite refinesE. Qed.

Global Instance refines_apply
  A B (R : A -> B -> Type) C D (R' : C -> D -> Type) :
  forall (c : A -> C) (d : B -> D), refines (R ==> R') c d ->
  forall (a : A) (b : B), refines R a b -> refines R' (c a) (d b) | 99.
Proof. by rewrite !refinesE => c d rcd a b rab; apply: rcd. Qed.

Global Instance composable_rid1 A B (R : A -> B -> Type) :
  composable eq R R | 1.
Proof.
rewrite composableE; apply: eq_hrelRL.
by split; [ apply: comp_eql | move=> x y hxy; exists x ].
Qed.

Global Instance composable_bool_id1 B (R : bool -> B -> Type) :
  composable bool_R R R | 1.
Proof. by rewrite composableE => x y [y' [[]]]. Qed.

(* Global Instance composable_nat_id1 B (R : nat -> B -> Type) :
  composable nat_R R R | 1. *)
(* Proof. by rewrite composableE => x y [y' [/nat_R_eq ->]]. Qed. *)

Global Instance composable_comp A B C (rAB : A -> B -> Type)
  (rBC : B -> C -> Type) : composable rAB rBC (rAB \o rBC).
Proof. by rewrite composableE. Qed.

Global Instance composable_imply A B C A' B' C'
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (R1 : A' -> B' -> Type)
  (R2 : B' -> C' -> Type) (R3 : A' -> C' -> Type) : composable R1 R2 R3 ->
  composable (rAB ==> R1) (rBC ==> R2) (rAB \o rBC ==> R3) | 0.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c [b [rABab rBCbc]].
apply: R123; exists (fB b); split; [ exact: RfAB | exact: RfBC ].
Qed.

Global Instance composable_imply_id1 A B A' B' C'
  (rAB : A -> B -> Type) (R1 : A' -> B' -> Type) (R2 : B' -> C' -> Type)
  (R3 : A' -> C' -> Type) : composable R1 R2 R3 ->
  composable (eq ==> R1) (rAB ==> R2) (rAB ==> R3) | 1.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c rABac.
apply: R123; exists (fB a); split; [ exact: RfAB | exact: RfBC ].
Qed.

(* Composable and pairs *)
Lemma prod_RE A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_R rA rB x y -> prod_hrel rA rB x y.
Proof. by case; split. Qed.

Lemma prod_RI A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_hrel rA rB x y -> prod_R rA rB x y.
Proof. by move: x y => [x1 x2] [y1 y2] [] /=; constructor. Qed.

Lemma refines_prod_R A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  refines rA x.1 y.1 -> refines rB x.2 y.2 -> refines (prod_R rA rB) x y.
Proof. by rewrite !refinesE => *; apply: prod_RI; split. Qed.

Global Instance composable_prod A A' B B' C C'
  (rAB : A -> B -> Type) (rAB' : A' -> B' -> Type)
  (rBC : B -> C -> Type) (rBC' : B' -> C' -> Type)
  (rAC : A -> C -> Type) (rAC' : A' -> C' -> Type) :
    composable rAB rBC rAC ->
    composable rAB' rBC' rAC' ->
    composable (prod_R rAB rAB') (prod_R rBC rBC')
               (prod_R rAC rAC') | 1.
Proof.
rewrite !composableE=> h1 h2 [a a'] [c c'] [[b b']].
move=> [/prod_RE [/= ??] /prod_RE [/= ??]].
by split; [ apply: h1; exists b | apply: h2; exists b'].
Qed.

Section refines_split.
Context {T} {Y} {Z} {R1 : T -> Y -> Type} {R2 : Y -> Z -> Type} {x : T} {z : Z}.

Lemma refines_split :
  refines (R1 \o R2) x z -> {y : Y & (refines R1 x y * refines R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split1 :
  refines (R1 \o R2) x z -> {y : Y & (refines R1 x y * R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split2 :
  refines (R1 \o R2) x z -> {y : Y & (R1 x y * refines R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

Lemma refines_split12 :
  refines (R1 \o R2) x z -> {y : Y & (R1 x y * R2 y z)%type}.
Proof. by rewrite !refinesE. Qed.

End refines_split.

Lemma refines_abstr A B C D (R : A -> B -> Type) (R' : C -> D -> Type)
      (c : A -> C) (d : B -> D):
        (forall (a :  A) (b : B), refines R a b -> refines R' (c a) (d b)) ->
        refines (R ==> R') c d.
Proof. by rewrite !refinesE; apply. Qed.

Lemma refines_abstr2 A B A' B' A'' B''
      (R : A -> B -> Type) (R' : A' -> B' -> Type) (R'' : A'' -> B'' -> Type)
      (f : A -> A' -> A'' ) (g : B -> B' -> B''):
        (forall (a : A)   (b : B), refines R a b ->
         forall (a' : A') (b' : B'), refines R' a' b' ->
        refines R'' (f a a') (g b b')) ->
        refines (R ==> R' ==> R'') f g.
Proof. by move=> H; do 2![eapply refines_abstr => *]; apply: H. Qed.

Global Instance refines_pair_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (rA ==> rB ==> prod_R rA rB)%rel (@pair _ _) (@pair _ _).
Proof. by rewrite refinesE. Qed.

Global Instance refines_fst_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_R rA rB ==> rA)%rel (@fst _ _) (@fst _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Global Instance refines_snd_R
  A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) :
  refines (prod_R rA rB ==> rB)%rel (@snd _ _) (@snd _ _).
Proof. by rewrite !refinesE=> [??] [??]. Qed.

Class unify A (x y : A) := unify_rel : x = y.
Global Instance unifyxx A (x : A) : unify x x := erefl.

Global Instance refines_of_unify A x y : unify x y -> refines (@unify A) x y | 100.
Proof. by rewrite refinesE. Qed.

Lemma refines_comp_unify A B (R : A -> B -> Type) x y :
  refines (R \o (@unify B))%rel x y -> refines R x y.
Proof. move=> /refines_split12.
  rewrite !refinesE=> H.
  case: H=> ? h.
  case: h=> ? h2.
  by rewrite -h2.
Qed.

End refinements.

Arguments refinesP {T T' R x y} _.

#[export] Hint Mode refines - - - + - : typeclass_instances.

#[export] Hint Extern 0 (refines _ _ _)
  => apply trivial_refines; eassumption : typeclass_instances.

#[export] Hint Extern 0 (refines (_ \o (@unify _))%rel _ _)
  => eapply refines_trans : typeclass_instances.

(* Tactic for doing parametricity proofs, it takes a parametricity
   theorem generated by the Parametricity plugin as argument *)
Ltac param x :=
  rewrite ?refinesE; do?move=> ?*;
  eapply x=> *; eapply refinesP;
  do ?eapply refines_apply; tc.

(* Special tactic when relation is defined using \o *)
Ltac param_comp x := eapply refines_trans; tc; param x.

Global Instance refines_true : refines _ _ _ :=
  trivial_refines bool_R_true_R.

Global Instance refines_false : refines _ _ _ :=
  trivial_refines bool_R_false_R.

Global Instance refines_negb : refines (bool_R ==> bool_R) negb negb.
Proof. exact/trivial_refines/negb_R. Qed.

Global Instance refines_implb : refines (bool_R ==> bool_R ==> bool_R) implb implb.
Proof. exact/trivial_refines/implb_R. Qed.

Global Instance refines_andb : refines (bool_R ==> bool_R ==> bool_R) andb andb.
Proof. exact/trivial_refines/andb_R. Qed.

Global Instance refines_orb : refines (bool_R ==> bool_R ==> bool_R) orb orb.
Proof. exact/trivial_refines/orb_R. Qed.

Global Instance refines_addb : refines (bool_R ==> bool_R ==> bool_R) addb addb.
Proof. exact/trivial_refines/addb_R. Qed.

Global Instance refines_eqb : refines (bool_R ==> bool_R ==> bool_R) eqtype.eq_op eqtype.eq_op.
Proof. exact/trivial_refines/eqb_R. Qed.

Lemma refines_goal (G G' : Type) : refines (fun T T' => T' -> T) G G' -> G' -> G.
Proof. by rewrite refinesE. Qed.

Global Instance refines_leibniz_eq (T : eqType) (x y : T) b :
  refines bool_R (x == y) b -> refines (fun T' T => T -> T') (x = y) b.
Proof. by move=> /refines_bool_eq; rewrite !refinesE => <- /eqP. Qed.

Module Refinements.

(* Generic operations *)
Module Op.

Class zero_of A := zero_op : A.
#[export] Hint Mode zero_of + : typeclass_instances.
Class one_of A := one_op : A.
#[export] Hint Mode one_of + : typeclass_instances.
Class opp_of A := opp_op : A -> A.
#[export] Hint Mode opp_of + : typeclass_instances.
Class add_of A := add_op : A -> A -> A.
#[export] Hint Mode add_of + : typeclass_instances.
Class sub_of A := sub_op : A -> A -> A.
#[export] Hint Mode sub_of + : typeclass_instances.
Class mul_of A := mul_op : A -> A -> A.
#[export] Hint Mode mul_of + : typeclass_instances.
Class exp_of A B := exp_op : A -> B -> A.
#[export] Hint Mode exp_of + + : typeclass_instances.
Class div_of A := div_op : A -> A -> A.
#[export] Hint Mode div_of + : typeclass_instances.
Class inv_of A := inv_op : A -> A.
#[export] Hint Mode inv_of + : typeclass_instances.
Class mod_of A := mod_op : A -> A -> A.
#[export] Hint Mode mod_of + : typeclass_instances.
Class scale_of A B := scale_op : A -> B -> B.
#[export] Hint Mode scale_of + + : typeclass_instances.

Class eq_of A := eq_op : A -> A -> bool.
#[export] Hint Mode eq_of + : typeclass_instances.
Class leq_of A := leq_op : A -> A -> bool.
#[export] Hint Mode leq_of + : typeclass_instances.
Class lt_of A := lt_op : A -> A -> bool.
#[export] Hint Mode lt_of + : typeclass_instances.
Class size_of A N := size_op : A -> N.
#[export] Hint Mode size_of + + : typeclass_instances.

Class spec_of A B   := spec : A -> B.
#[export] Hint Mode spec_of + + : typeclass_instances.
Definition spec_id {A : Type} : spec_of A A := id.
Class implem_of A B := implem : A -> B.
#[export] Hint Mode implem_of + + : typeclass_instances.
Definition implem_id {A : Type} : implem_of A A := id.
Class cast_of A B  := cast_op : A -> B.
#[export] Hint Mode cast_of + + : typeclass_instances.

End Op.
End Refinements.

Import Refinements.Op.

#[export]
Typeclasses Transparent zero_of one_of opp_of add_of sub_of mul_of exp_of div_of
            inv_of mod_of scale_of size_of eq_of leq_of lt_of spec_of implem_of cast_of.

Arguments spec / A B spec_of _: assert.

Notation "0"      := zero_op        : computable_scope.
Notation "1"      := one_op         : computable_scope.
Notation "-%C"    := opp_op.
Notation "- x"    := (opp_op x)     : computable_scope.
Notation "+%C"    := add_op.
Notation "x + y"  := (add_op x y)   : computable_scope.
Notation "x - y"  := (sub_op x y)   : computable_scope.
Notation "*%C"    := mul_op.
Notation "x * y"  := (mul_op x y)   : computable_scope.
Notation "x ^ y"  := (exp_op x y)   : computable_scope.
Notation "x %/ y" := (div_op x y)   : computable_scope.
Notation "x ^-1"  := (inv_op x)     : computable_scope.
Notation "x %% y" := (mod_op x y)   : computable_scope.
Notation "*:%C"   := scale_op.
Notation "x *: y" := (scale_op x y) : computable_scope.
Notation "x == y" := (eq_op x y)    : computable_scope.
Notation "x <= y" := (leq_op x y)   : computable_scope.
Notation "x < y"  := (lt_op x y)    : computable_scope.
Notation cast     := (@cast_op _).

Ltac simpC :=
  do ?[ rewrite -[0%C]/0%R
      | rewrite -[1%C]/1%R
      | rewrite -[(_ + _)%C]/(_ + _)%R
      | rewrite -[(_ + _)%C]/(_ + _)%N
      | rewrite -[(- _)%C]/(- _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%N
      | rewrite -[(_ * _)%C]/(_ * _)%R
      | rewrite -[(_ * _)%C]/(_ * _)%N
      | rewrite -[(_ %/ _)%C]/(_ %/ _)%R
      | rewrite -[(_ %% _)%C]/(_ %% _)%R
      | rewrite -[(_ == _)%C]/(_ == _)%bool
      ].

(* Section testmx. *)
(* Variable mxA : nat -> nat -> Type. *)
(* Definition idmx (m n : nat) (mx : mxA m n) : mxA m n := mx. *)
(* End testmx. *)
(* Parametricity idmx. *)
(* Print idmx_R. (* Here we get something too general! *) *)



(* Workaround because casts are not retained for hypothesis, so we
design this elimination lemma to abstract the context and vm_compute in the goal *)
Lemma abstract_context T (P : T -> Type) x : (forall Q, Q = P -> Q x) -> P x.
Proof. by move=> /(_ P); apply. Qed.

Tactic Notation  "context" "[" ssrpatternarg(pat) "]" tactic3(tac) :=
  let H := fresh "H" in let Q := fresh "Q" in let eqQ := fresh "eqQ" in
  ssrpattern pat => H;
  elim/abstract_context : (H) => Q eqQ; rewrite /H {H};
  tac; rewrite eqQ {Q eqQ}.

Class strategy_class (C : forall T, T -> T -> Prop) :=
   StrategyClass : C = @eq.
#[export] Hint Mode strategy_class + : typeclass_instances.

Class native_compute T (x y : T) := NativeCompute : x = y.
#[export] Hint Mode native_compute - + - : typeclass_instances.
#[export] Hint Extern 0 (native_compute _ _) =>
  context [(X in native_compute X)] native_compute; reflexivity :
  typeclass_instances.
#[global]
Instance strategy_class_native_compute : strategy_class native_compute := erefl.

Class vm_compute T (x y : T) := VmCompute : x = y.
#[export] Hint Mode vm_compute - + - : typeclass_instances.
#[export] Hint Extern 0 (vm_compute _ _) =>
  context [(X in vm_compute X)] vm_compute; reflexivity :
  typeclass_instances.
#[global]
Instance strategy_class_vm_compute : strategy_class vm_compute := erefl.

Class compute T (x y : T) := Compute : x = y.
#[export] Hint Mode compute - + - : typeclass_instances.
#[export] Hint Extern 0 (compute _ _) =>
  context [(X in compute X)] compute; reflexivity :
  typeclass_instances.
#[global] Instance strategy_class_compute : strategy_class compute := erefl.

Class simpl T (x y : T) := Simpl : x = y.
#[export] Hint Mode simpl - + - : typeclass_instances.
#[export] Hint Extern 0 (simpl _ _) =>
  context [(X in simpl X)] simpl; reflexivity :
  typeclass_instances.
#[global] Instance strategy_class_simpl : strategy_class simpl := erefl.

Lemma coqeal_eq C {eqC : strategy_class C} {T T'} spec (x x' : T) {y y' : T'}
   {rxy : refines eq (spec_id x) (spec y)}  {ry : C _ y y'}
   {rx : simpl (spec y') x'} : x = x'.
Proof. by rewrite eqC in ry; rewrite -rx -ry; apply: refines_eq. Qed.

Notation "'[' 'coqeal'  strategy  'of'  x ']'" :=
  (@coqeal_eq strategy _ _ _ _ x _ _ _ _ _ _).
Notation coqeal strategy := [coqeal strategy of _].
Notation "'[' 'coqeal'  strategy  'of'  x  'for'  y ']'" :=
  ([coqeal strategy of x] : y = _).

Ltac coqeal := apply: refines_goal; vm_compute.
Tactic Notation "coqeal_" tactic3(tac) :=  apply: refines_goal; tac.
Tactic Notation "coqeal" "[" ssrpatternarg(pat) "]" open_constr(strategy) :=
  let H := fresh "H" in let Q := fresh "Q" in let eqQ := fresh "eqQ" in
  ssrpattern pat => H; elim/abstract_context : (H) => Q eqQ;
  rewrite /H {H} [(X in Q X)](coqeal strategy) eqQ {Q eqQ}.

Ltac refines_apply1 := eapply refines_apply; tc.
Ltac refines_abstr1 := eapply refines_abstr=> ???; tc.
Ltac refines_apply := do ![refines_apply1].
Ltac refines_abstr := do ![refines_abstr1].
Ltac refines_trans :=  eapply refines_trans; tc.

(** Automation: for proving refinement lemmas involving if-then-else's
do [rewrite !ifE; apply refines_if_expr]. *)
Lemma refines_if_expr
  (A C : Type) (b1 b2 : bool) (vt1 vf1 : A) (vt2 vf2 : C) (R : A -> C -> Type) :
  refines bool_R b1 b2 -> (b1 -> b2 -> R vt1 vt2) -> (~~ b1 -> ~~ b2 -> R vf1 vf2) ->
  refines R (if_expr b1 vt1 vf1) (if_expr b2 vt2 vf2).
Proof.
move/refines_bool_eq/refinesP=> Hb; rewrite -!{}Hb => Ht Hf.
rewrite /if_expr !refinesE; case: b1 Ht Hf => Ht Hf.
exact: Ht.
exact: Hf.
Qed.

Lemma optionE (A B : Type) (o : option A) (b : B) (f : A -> B) :
  match o with
  | Some a => f a
  | None => b
  end = oapp f b o.
Proof. by []. Qed.

(** Automation: for proving refinement lemmas involving options,
do [rewrite !optionE; refines_apply]. *)
Global Instance refines_option
  (A B : Type) (rA : A -> A -> Type) (rB : B -> B -> Type) :
  refines ((rA ==> rB) ==> rB ==> option_R rA ==> rB) (@oapp _ _) (@oapp _ _).
Proof.
rewrite refinesE => f1 f2 Hf b1 b2 Hb o1 o2 Ho.
case: o1 Ho => [a1|]; case: o2 => [a2|] Ho //=.
{ eapply refinesP; refines_apply; rewrite refinesE in Ho *.
  by inversion_clear Ho. }
{ by eapply refinesP; inversion_clear Ho. }
{ by eapply refinesP; inversion_clear Ho. }
Qed.
