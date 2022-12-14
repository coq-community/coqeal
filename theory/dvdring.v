(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From Coq Require Import ssreflect ssrfun ssrbool Arith.Wf_nat.
From mathcomp Require Import eqtype ssrnat div seq path.
From mathcomp Require Import ssralg fintype perm tuple choice generic_quotient.
From mathcomp Require Import matrix bigop zmodp mxalgebra poly.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* tools for Acc induction *)

Scheme acc_dep := Induction for Acc Sort Type.

Lemma ssr_lt_wf : well_founded (fun x y => x < y).
Proof. by apply: (well_founded_lt_compat _ id)=>x y /ltP. Defined.

Section GUARD.
Variable A: Type.
Variable P : A -> A -> Prop.

Fixpoint guarded (n: nat) (Wf: well_founded P) : well_founded P :=
  if n is m.+1 then
    fun x =>
      @Acc_intro _ _ x (fun y _ => guarded m (guarded m Wf) y)
  else Wf.
End GUARD.


(** Explicit divisibility ring *)
Module DvdRing.

(* Specification of division: div_spec a b == b | a *)
Variant div_spec (R : ringType) (a b : R) : option R -> Type :=
| DivDvd x of a = x * b : div_spec a b (Some x)
| DivNDvd of (forall x, a != x * b) : div_spec a b None.

Record mixin_of (R : ringType) : Type := Mixin {
  div : R -> R -> option R;
  _ : forall a b, div_spec a b (div a b)
  }.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : GRing.IntegralDomain.class_of R;
  mixin : mixin_of (GRing.IntegralDomain.Pack base)
}.
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@GRing.IntegralDomain.Pack T b0)) :=
  fun bT b & phant_id (GRing.IntegralDomain.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m).

Definition eqType := Equality.Pack class.
Definition choiceType := Choice.Pack class.
Definition zmodType := GRing.Zmodule.Pack class.
Definition ringType := GRing.Ring.Pack class.
Definition comRingType := GRing.ComRing.Pack class.
Definition unitRingType := GRing.UnitRing.Pack class.
Definition comUnitRingType := GRing.ComUnitRing.Pack class.
Definition idomainType := GRing.IntegralDomain.Pack class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Notation dvdRingType := type.
Notation DvdRingType T m := (@pack T _ m _ _ id _ id).
Notation DvdRingMixin := Mixin.
Notation "[ 'dvdRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'dvdRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'dvdRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'dvdRingType'  'of'  T ]") : form_scope.
End Exports.

End DvdRing.
Export DvdRing.Exports.

Definition odivr R := DvdRing.div (DvdRing.class R).
Definition dvdr R a b := @odivr R b a : bool.
Definition eqd (R : dvdRingType) (a b : R) := (dvdr a b) && (dvdr b a).

Definition sdvdr (R : dvdRingType) (x y : R) := (dvdr x y) && ~~(dvdr y x).

Module Notations.

Notation "%=R" := (@eqd _) : ring_scope.
Notation "a %= b" := (@eqd _ a b) (at level 70, no associativity): ring_scope.
Notation "%|%R" := (@dvdr _) : ring_scope.
Notation "a %| b" := (dvdr a b) : ring_scope.
Notation "%/?%R" := (@odivr _) : ring_scope.
Notation "a %/? b" := (odivr a b)
  (at level 70, no associativity): ring_scope.

Notation "%<|R" := (@sdvdr _).
Notation "x %<| y" := (sdvdr x y) (at level 70, no associativity).

End Notations.
Export Notations.

Section DvdRingTheory.

Variable R : dvdRingType.

Implicit Types a b c : R.

(** Properties of odivr *)

Lemma odivrP : forall a b, DvdRing.div_spec a b (a %/? b).
Proof. by case: R=> [? [? []]] /=. Qed.

Lemma odiv0r a : a != 0 -> 0 %/? a = Some 0.
Proof.
case: odivrP=> [x|H _]; last by move: (H 0); rewrite mul0r eqxx.
by move/eqP; rewrite eq_sym mulf_eq0 orbC; case: eqP => //= _ /eqP->.
Qed.

Lemma odivr0 a : a != 0 -> a %/? 0 = None.
Proof.
by case: odivrP=> // x; rewrite mulr0=> ->; rewrite eqxx.
Qed.

Lemma odivr1 a : a %/? 1 = Some a.
Proof.
case: odivrP=> [x|H]; first by rewrite mulr1=> ->.
by move: (H a); rewrite mulr1 eqxx.
Qed.

Lemma odivrr a : a != 0 -> a %/? a = Some 1.
Proof.
move=> a0; case: odivrP=> [x|H].
  by rewrite -{1}[a]mul1r; move/(mulIf a0) <-.
by move: (H 1); rewrite mul1r eqxx.
Qed.

Lemma odivr_mulrK a b : a != 0 -> b * a %/? a = Some b.
Proof.
move=> a0; case: odivrP=> [x|H]; first by move/(mulIf a0) ->.
by move: (H b); rewrite eqxx.
Qed.

Lemma odivr_mulKr a b : a != 0 -> a * b %/? a = Some b.
Proof. by move=> a0; rewrite mulrC odivr_mulrK. Qed.

Lemma odivr_mul2l a b c : a != 0 -> b != 0 -> a * b %/? (a * c) = (b %/? c).
Proof.
move=> a0 b0.
case c0: (c == 0); first by rewrite (eqP c0) mulr0 !odivr0 // mulf_neq0.
case: odivrP=> [x|H].
  rewrite mulrCA; move/(mulfI a0).
  case: (odivrP b c)=> [x' ->|H]; first by move/(mulIf (negbT c0)) ->.
  by move=> Hbxc; move: (H x); rewrite Hbxc eqxx.
by case: odivrP=> //x Hbxc; move: (H x); rewrite mulrCA Hbxc eqxx.
Qed.

Lemma odivr_mul2r a b c : a != 0 -> b != 0 -> b * a %/? (c * a) = (b %/? c).
Proof. by move=> a0 b0; rewrite mulrC [_ * a]mulrC odivr_mul2l. Qed.

Lemma odivr_some a b c : a %/? b = Some c -> a = b * c.
Proof. by case: odivrP=>// x -> [<-]; rewrite mulrC. Qed.

(** Properties of dvdr *)

Lemma dvdrP a b : reflect (exists x, b = x * a) (a %| b).
Proof.
rewrite /dvdr; case: odivrP=> //= [x|] hx; constructor; first by exists x.
by case=> x /eqP; apply: negP.
Qed.

(****)
Lemma eqdP a b :
  reflect (exists2 c12 : R, (c12 \is a GRing.unit) & c12 * a = b) (a %= b).
Proof.
apply: (iffP andP).
  case=> /dvdrP [x Hx] /dvdrP [y Hy].
  case: (eqVneq b 0) => Hb.
    rewrite Hb mulr0 in Hy.
    by exists 1; rewrite ?unitr1 // Hy mulr0 Hb.
  exists x; last by rewrite Hx.
  apply/GRing.unitrPr; exists y.
  rewrite Hy mulrA in Hx.
  by apply: (mulIf Hb); rewrite -Hx mul1r.
case=> c Hc H; split; apply/dvdrP.
  by exists c; rewrite H.
exists (c^-1); apply: (@mulfI _ c).
  by apply/eqP=> Habs; rewrite Habs unitr0 in Hc.
by rewrite mulrA mulrV // mul1r.
Qed.
(****)

Lemma dvdrr a : a %| a.
Proof. by apply/dvdrP; exists 1; rewrite mul1r. Qed.

Hint Resolve dvdrr : core.

Lemma dvdr_trans : transitive (@dvdr R).
Proof.
move=> b a c; case/dvdrP=> x ->; case/dvdrP=> y ->.
by apply/dvdrP; exists (y * x); rewrite mulrA.
Qed.

Lemma dvdr0 a : a %| 0.
Proof. by apply/dvdrP; exists 0; rewrite mul0r. Qed.

Lemma dvd0r a : (0 %| a) = (a == 0) :> bool.
Proof.
apply/idP/idP; last by move/eqP->.
by case/dvdrP=> x; rewrite mulr0=> ->.
Qed.

Lemma dvdr_add a b c : a %| b -> a %| c -> a %| b + c.
Proof.
case/dvdrP=>x bax; case/dvdrP=>y cay.
by apply/dvdrP; exists (x + y); rewrite mulrDl bax cay.
Qed.

Lemma dvdrN a b : (a %| - b) = (a %| b).
Proof.
apply/dvdrP/dvdrP=> [] [x hx]; exists (-x); first by rewrite mulNr -hx opprK.
by rewrite hx mulNr.
Qed.

Lemma dvdNr a b : (- a %| b) = (a %| b).
Proof.
apply/dvdrP/dvdrP=> [] [x ->]; exists (-x); rewrite ?mulrNN //.
by rewrite mulNr mulrN.
Qed.

Lemma dvdrNN a b : (- a %| - b) = (a %| b).
Proof. by rewrite dvdNr dvdrN. Qed.

Lemma dvdr_sub a b c : a %| b -> a %| c -> a %| b - c.
Proof. by move=> ab ac; rewrite dvdr_add // dvdrN. Qed.

Lemma dvdr_addl a b c : b %| a -> (b %| c + a) = (b %| c).
Proof.
move=> ba; apply/idP/idP=> ha; last exact: dvdr_add.
by rewrite -[c](addrK a) dvdr_sub.
Qed.

Lemma dvdr_addr a b c : b %| a -> (b %| a + c) = (b %| c).
Proof. by move=> ba; rewrite addrC dvdr_addl. Qed.

Lemma dvdr_add_eq a b c : a %| b + c -> (a %| b) = (a %| c).
Proof. by move=> ha; rewrite -[b](addrK c) dvdr_addr // dvdrN. Qed.

Lemma dvdr_mull c a b : a %| b -> a %| c * b.
Proof. by case/dvdrP=> x ->; apply/dvdrP; exists (c * x); rewrite mulrA. Qed.

Lemma dvdr_mulr b a c : a %| c -> a %| c * b.
Proof. by move=> hac; rewrite mulrC dvdr_mull. Qed.

Lemma dvdr_mul c d a b : a %| c -> b %| d -> a * b %| c * d.
Proof.
case/dvdrP=>x ->; case/dvdrP=> y ->.
by rewrite -mulrCA; apply/dvdrP; exists (y * x); rewrite !mulrA.
Qed.

Lemma dvdr_mul2r c a b : c != 0 -> (a * c %| b * c) = (a %| b) :> bool.
Proof.
move=> c0; apply/idP/idP=> [|hab]; last exact: dvdr_mul.
case/dvdrP=> x /eqP; rewrite mulrA (inj_eq (mulIf _)) // => /eqP ->.
exact: dvdr_mull.
Qed.

Lemma dvdr_mul2l c a b : c != 0 -> (c * a %| c * b) = (a %| b) :> bool.
Proof. by move=> c0; rewrite ![c * _]mulrC dvdr_mul2r. Qed.

Lemma dvd1r a : 1 %| a.
Proof. by apply/dvdrP; exists a; rewrite mulr1. Qed.

Hint Resolve dvd1r : core.

(* Sorted and dvdr *)
Lemma sorted_dvd0r (s : seq R) : sorted %|%R (0 :: s) -> all (eq_op^~ 0) s.
Proof.
move/(order_path_min dvdr_trans)/(all_nthP 0)=> hi.
by apply/(all_nthP 0) => i his; rewrite -dvd0r; apply: hi.
Qed.

Lemma sorted_cons (a : R) s : sorted %|%R s -> a %| s`_0 -> sorted %|%R (a :: s).
Proof. by elim: s a=> //= a s ih a'; rewrite /nth => -> ->. Qed.

Lemma sorted_nth0 (s : seq R) : sorted %|%R s -> forall i, s`_0 %| s`_i.
Proof.
case: s=> [_|a s hi] [|i] /=; do? by rewrite dvdrr.
have [his|hsi] := ltnP i (size s); last by rewrite nth_default // dvdr0.
by move/(order_path_min dvdr_trans)/(all_nthP 0): hi => ->.
Qed.

(** Properties of eqd *)

Lemma eqd_def : forall a b, a %= b = (a %| b) && (b %| a).
Proof. by []. Qed.

Lemma eqdd a : a %= a.
Proof. by rewrite eqd_def dvdrr. Qed.

Hint Resolve eqdd : core.

Lemma eqd_sym : symmetric (@eqd R).
Proof. by move=> a b; rewrite eqd_def; apply/andP/andP; case. Qed.

Hint Resolve eqd_sym : core.

Lemma eqd_trans : transitive (@eqd R).
Proof.
move=> a b c; rewrite !eqd_def; case/andP=> ba ab; case/andP=> ac ca.
by rewrite (dvdr_trans ba) // (dvdr_trans ca).
Qed.

(* Canonical Structure eqd_Equiv := EquivRel eqdd eqd_sym eqd_trans. *)

(* uncomment it when the proof won't get stuck *)

Lemma congr_eqd b d a c : a %= b -> c %= d -> (a %= c) = (b %= d).
Proof.
move=> ab cd; apply/idP/idP=> [ac|bd].
  by rewrite eqd_sym in ab; rewrite (eqd_trans (eqd_trans ab ac) cd).
by rewrite eqd_sym in cd; rewrite (eqd_trans ab (eqd_trans bd cd)).
(* Not working: *)
(* by move=> b d a c ab cd; rewrite !equivE (equivP ab) (equivP cd). *)
Qed.

(* Local Notation DR := {R %/ %=R}. *)

Lemma eqdr0 a : (a %= 0) = (a == 0).
Proof. by rewrite eqd_def dvdr0 dvd0r. Qed.

Lemma eqd0r a : (0 %= a) = (a == 0).
Proof. by rewrite eqd_def dvdr0 dvd0r andbT. Qed.

Lemma eq_eqd a b : a = b -> a %= b.
Proof. by move->. Qed.

Lemma eqd_mul c d a b : a %= c -> b %= d -> a * b %= c * d.
Proof. by rewrite /eqd; do 2!case/andP=> ? ?; rewrite !dvdr_mul. Qed.

(* Print Canonical Projections. *)
(* Lemma mulqr_pi : forall  a a' b b', a = a' %{m DR} -> b = b' %{m DR} *)
(*   -> a * b = a' * b' %{m DR}. *)
(* Proof. *)
(* move=> a a' b b'. move/equivP; move/eqd_mul2rW. *)
(* Proof. *)
(* move=> a b /=; rewrite /mulqr. *)
(* rewrite (equivP (@eqd_mul2rW a _ _ _)) ?equivE ?reprK //.  *)
(* by rewrite (equivP (@eqd_mul2lW b _ _ _)) ?equivE ?reprK.  *)
(* Qed. *)

(* Definition mulqr (a b : DR) : DR := (\pi ((repr a) * (repr b))). *)

(* Local Notation "x *d y" := (mulqr x y) *)
(*   (at level 40, left associativity, format "x  *d  y"). *)

(* Lemma mulqr_pi : forall a b, (\pi a) *d (\pi b) = \pi (a * b). *)
(* Proof. *)
(* move=> a b /=; rewrite /mulqr. *)
(* rewrite (equivP (@eqd_mul2rW a _ _ _)) ?equivE ?reprK //.  *)
(* by rewrite (equivP (@eqd_mul2lW b _ _ _)) ?equivE ?reprK.  *)
(* Qed. *)

(* Lemma mulqr_pi : forall a b, (\pi a) *d (\pi b) = \pi (a * b). *)
(* Proof. *)
(* move=> a b /=; rewrite /mulqr. *)
(* rewrite (equivP (@eqd_mul2rW a _ _ _)) ?equivE ?reprK //. *)
(* by rewrite (equivP (@eqd_mul2lW b _ _ _)) ?equivE ?reprK. *)
(* Qed. *)

(* Lemma mulqr1 : forall x, x *d \pi_DR 1 = x. *)
(* by elim/quotW=> x; rewrite mulqr_pi mulr1. Qed. *)

(* Lemma mulq1r : forall x, \pi_DR 1 *d x = x. *)
(* by elim/quotW=> x; rewrite mulqr_pi mul1r. Qed. *)


(* Lemma eqd_mul : forall a b c d, a %= b -> c %= d -> a * c %= b * d. *)
(* Proof. by move=> ????; rewrite !equivE -!mulqr_pi; move/eqP->; move/eqP->. Qed. *)

Lemma eqd_mul2l c a b : c != 0 -> (c * a %= c * b) = (a %= b).
Proof. by move=> c0; rewrite eqd_def !dvdr_mul2l. Qed.

Lemma eqd_mul2r c a b : c != 0 -> (a * c %= b * c) = (a %= b).
Proof. by move=> c0; rewrite eqd_def !dvdr_mul2r. Qed.

Lemma eqd_dvd c d a b : a %= c -> b %= d -> (a %| b) = (c %| d).
Proof.
rewrite !eqd_def; case/andP=> ac ca; case/andP=> bd db.
apply/idP/idP=> [ab|cd]; first exact: (dvdr_trans ca (dvdr_trans ab bd)).
exact: (dvdr_trans ac (dvdr_trans cd db)).
Qed.

(****)
Lemma eqd_dvdr b a c : a %= b -> (c %| a) = (c %| b).
Proof. exact: eqd_dvd. Qed.

Lemma eqd_dvdl b a c : a %= b -> (a %| c) = (b %| c).
Proof. by move/eqd_dvd; apply. Qed.

Lemma eqd_ltrans : left_transitive (@eqd R).
Proof. exact: (left_trans eqd_sym eqd_trans). Qed.

Lemma eqd_rtrans : right_transitive (@eqd R).
Proof. exact: (right_trans eqd_sym eqd_trans). Qed.

Lemma eqd_mulr b a c : a %= b -> a * c %= b * c.
Proof. by move/eqd_mul; apply. Qed.

Lemma eqd_mull b a c : a %= b -> c * a %= c * b.
Proof. exact: eqd_mul. Qed.
(****)

(* dvdr + unit *)
Lemma dvdr1 a : (a %| 1) = (a %= 1).
Proof. by rewrite /eqd dvd1r andbT. Qed.

Lemma unitd1 a : (a \is a GRing.unit) = (a %= 1).
Proof.
rewrite -dvdr1; apply/unitrP/dvdrP => [[x [Hxa1 _]]|[x H]]; exists x => //.
by split=> //; rewrite mulrC.
Qed.

Lemma eqd1 a : a \in GRing.unit -> a %= 1.
Proof. by rewrite unitd1. Qed.

(* Lemma dvdr_mulUr_r : forall x a b, x \in GRing.unit *)
(*   -> (a %| x * b) = (a %| b) :> bool. *)
(* Proof. *)
(* move=> x a b ux; rewrite -!(dvdqr_pi, mulqr_pi) (equivP (unit_eqd1 ux)). *)
(* by rewrite mulqr_pi !dvdqr_pi mul1r. *)
(* Qed. *)

(* Lemma dvdr_mulrU_r : forall x a b, x \in GRing.unit *)
(*   -> (a %| b * x) = (a %| b) :> bool. *)
(* Proof. by move=> x a b; rewrite mulrC; apply: dvdr_mulUr_r. Qed. *)

(* Lemma dvdr_mulUr_l : forall x a b, x \in GRing.unit -> *)
(*   (x * b %| a) = (b %| a) :> bool. *)
(* Proof. *)
(* move=> x a b; rewrite -eqd1. *)
(* by move/(eqd_mul2rW b); move/eqd_dvdr->; rewrite mul1r. *)
(* Qed. *)

(* Lemma dvdr_mulrU_l : forall x a b, x \in GRing.unit *)
(*   -> (b * x %| a) = (b %| a) :> bool. *)
(* Proof. by move=> x a b; rewrite mulrC; apply: dvdr_mulUr_l. Qed. *)

Lemma dvdUr a b : a %= 1 -> a %| b.
Proof. by move=> a1; rewrite (eqd_dvd a1 (eqdd _)) dvd1r. Qed.

Lemma dvdrU b a : b %= 1 -> a %| b = (a %= 1).
Proof. by move=> b1; rewrite (eqd_dvd (eqdd _) b1) dvdr1. Qed.

Lemma dvdr_mulr_l b a : b != 0 -> (a * b %| b) = (a %= 1).
Proof. by move=> b0; rewrite -{2}[b]mul1r dvdr_mul2r ?dvdr1. Qed.

Lemma dvdr_mull_l b a : b != 0 -> (b * a %| b) = (a %= 1).
Proof. by move=> b0; rewrite mulrC dvdr_mulr_l. Qed.

(*
Lemma dvdr_expl : forall a b, ~(a %| b) \/ (exists x, b = a*x).
Proof.
move=> a b; case H: (a %| b); last by constructor.
by constructor 2; move: H; case/dvdrP=>x bax; exists x.
Qed.
*)

(* eqd + unit *)
(*
Lemma eqd_mulUr : forall a b x, a %= b * x -> x \in GRing.unit -> a %= b.
Proof.
move=> a b x; rewrite /eqd; case/andP=>abx bxa xU.
apply/andP; split; first exact: dvdr_mulUr xU abx.
by case/dvdrP: bxa=> x' H; apply/dvdrP; exists (x*x'); rewrite mulrA.
Qed.

Lemma eqd_mulUl : forall a b x, a %= x * b -> x \in GRing.unit -> a %= b.
Proof. by move=> a b x; rewrite mulrC; apply: eqd_mulUr. Qed.

Lemma eqdU1 : forall a, (a \in GRing.unit) = (a %= 1).
Proof.
by move=> a; apply/idP/idP; rewrite /eqd dvdr1 dvd1r; [move=> ->|case/andP].
Qed.
*)

(** Properties of sdvdr *)

Lemma sdvdr_def : forall a b, a %<| b = (a %| b) && ~~(b %| a).
Proof. by []. Qed.

Lemma sdvdrW a b : a %<| b -> a %| b.
Proof. by case/andP. Qed.

Lemma sdvdrNW a b : a %<| b -> ~~(b %| a).
Proof. by case/andP. Qed.

Lemma sdvdr0 a : a %<| 0 = (a != 0).
Proof. by rewrite sdvdr_def dvdr0 dvd0r. Qed.

Lemma sdvd0r a : 0 %<| a = false.
Proof. by rewrite sdvdr_def dvdr0 andbF. Qed.

(****)
(** bigop **)

Lemma big_dvdr (I : finType) (d : R) (F : I -> R) (P : pred I) :
  (forall i,  d %| F i) -> d %| \sum_(i : I | P i) (F i).
Proof.
move=> H; elim: (index_enum I)=> [|a l IHl].
  by rewrite big_nil dvdr0.
rewrite big_cons; case: (P a).
  by rewrite dvdr_addl; [apply: H | apply: IHl].
exact: IHl.
Qed.

Lemma eqd_big_mul n (P : pred 'I_n) (F1 F2 : 'I_n -> R) :
  (forall i, P i -> F1 i %= F2 i) ->
  \prod_(i | P i) F1 i %= \prod_(i | P i) F2 i.
Proof.
apply: (big_ind2 (@eqd R))=> // a b c d.
exact: eqd_mul.
Qed.


Lemma eqd_big_mul1 n (P : pred 'I_n) (F : 'I_n -> R) :
   \prod_(i < n | P i) F i %= 1 -> (forall i, P i -> F i %= 1).
Proof.
case: n P F=> [ ? ? ? []|n P F Hb i Hi] //.
rewrite (bigD1 i) //= -unitd1 unitrM unitd1 in Hb.
by case/andP: Hb.
Qed.
(****)

(*** Matrix *)
Lemma dvdr_mulmxr m n p x (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)) :
  (forall i j, x %| M i j) -> forall i j, x %| (M *m N) i j.
Proof.
by move=> hM i j; rewrite !mxE; apply: big_dvdr=> k; rewrite dvdr_mulr ?hM.
Qed.

Lemma dvdr_mulmxl m n p x (M : 'M[R]_(m,n)) (N : 'M[R]_(p,m)) :
  (forall i j, x %| M i j) -> forall i j, x %| (N *m M) i j.
Proof.
by move=> hM i j; rewrite !mxE; apply: big_dvdr=> k; rewrite dvdr_mull ?hM.
Qed.

Lemma dvdr_usubmx m0 m1 n0 n1 x (M : 'M[R]_(m0 + m1,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (usubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

Lemma dvdr_dsubmx m0 m1 n0 n1 x (M : 'M[R]_(m0 + m1,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (dsubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

Lemma dvdr_rsubmx m0 m1 n0 n1 x (M : 'M[R]_(m0 + m1,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (rsubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

Lemma dvdr_lsubmx m0 n0 n1 x (M : 'M[R]_(m0,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (lsubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

Lemma dvdr_ulsubmx m0 m1 n0 n1 x (M : 'M[R]_(m0 + m1,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (ulsubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

Lemma dvdr_ursubmx m0 m1 n0 n1 x (M : 'M[R]_(m0 + m1,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (ursubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

Lemma dvdr_dlsubmx m0 m1 n0 n1 x (M : 'M[R]_(m0 + m1,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (dlsubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

Lemma dvdr_drsubmx m0 m1 n0 n1 x (M : 'M[R]_(m0 + m1,n0 + n1)) :
  (forall i j, x %| M i j) -> forall i j, x %| (drsubmx M) i j.
Proof. by move=> hM i j; rewrite !mxE. Qed.

(* TODO: Prove other direction *)
Lemma dvdr_col_mx m n p x (M : 'M[R]_(m,n)) (N : 'M[R]_(p,n)) :
  (forall i j, x %| M i j) /\ (forall i j, x %| N i j) ->
  forall i j, x %| (col_mx M N) i j.
Proof.
case=> h1 h2 i j; rewrite !mxE; case: splitP=> k {i}_.
  exact: (h1 k j).
exact: (h2 k j).
Qed.

(* TODO: Prove other direction *)
Lemma dvdr_row_mx m n p x (M : 'M[R]_(m,n)) (N : 'M[R]_(m,p)) :
  (forall i j, x %| M i j) /\ (forall i j, x %| N i j) ->
  forall i j, x %| (row_mx M N) i j.
Proof.
case=> h1 h2 i j; rewrite !mxE; case: splitP=> k {j}_.
  exact: (h1 i k).
exact: (h2 i k).
Qed.

End DvdRingTheory.

Hint Resolve dvdrr dvd1r eqdd : core.

(* Notation "x *d y" := (mulqr x y) *)
(*   (at level 40, left associativity, format "x  *d  y"). *)

(* Notation "x %|d y" := (dvdqr x y) *)
(*   (at level 40, left associativity, format "x  %|d  y"). *)

Module GcdDomain.

Record mixin_of (R : dvdRingType) : Type := Mixin {
  gcdr : R -> R -> R;
  _ : forall d a b, d %| gcdr a b = (d %| a) && (d %| b)
}.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : DvdRing.class_of R;
  mixin : mixin_of (DvdRing.Pack base)
}.
Local Coercion base : class_of >-> DvdRing.class_of.

(* Structure = Record *)
Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@DvdRing.Pack T b0)) :=
  fun bT b & phant_id (DvdRing.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m).

Definition eqType := Equality.Pack class.
Definition choiceType := Choice.Pack class.
Definition zmodType := GRing.Zmodule.Pack class.
Definition ringType := GRing.Ring.Pack class.
Definition comRingType := GRing.ComRing.Pack class.
Definition unitRingType := GRing.UnitRing.Pack class.
Definition comUnitRingType := GRing.ComUnitRing.Pack class.
Definition idomainType := GRing.IntegralDomain.Pack class.
Definition dvdRingType := DvdRing.Pack class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> DvdRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion dvdRingType : type >-> DvdRing.type.
Canonical Structure dvdRingType.
Notation gcdDomainType := type.
Notation GcdDomainType T m := (@pack T _ m _ _ id _ id).
Notation GcdDomainMixin := Mixin.
Notation "[ 'gcdDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'gcdDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'gcdDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'gcdDomainType'  'of'  T ]") : form_scope.
End Exports.

End GcdDomain.
Export GcdDomain.Exports.

Definition gcdr R := GcdDomain.gcdr (GcdDomain.class R).

Definition lcmr R a b := nosimpl
  (if (a == 0) || (b == 0) then 0 else odflt 0 ((a * b) %/? (@gcdr R a b))).

Definition gcdsr R := foldr (@gcdr R) 0.
Definition lcmsr R := foldr (@lcmr R) 1.

(* Definition gcdqr (R : gcdDomainType) (a b : {R %/ %=R}) : {R %/ %=R} := *)
(*   (\pi (gcdr (repr a) (repr b))). *)

Section GCDDomainTheory.

Variable R : gcdDomainType.

Implicit Types a b : R.

Lemma dvdr_gcd : forall d a b, d %| gcdr a b = (d %| a) && (d %| b) :> bool.
Proof. by case: R=> [? [? []]]. Qed.

Lemma dvdr_gcdl a b : gcdr a b %| a.
Proof. by move: (dvdrr (gcdr a b)); rewrite dvdr_gcd; case/andP. Qed.

Lemma dvdr_gcdr a b : gcdr a b %| b.
Proof. by move: (dvdrr (gcdr a b)); rewrite dvdr_gcd; case/andP. Qed.

Lemma gcdr_eq0 a b : (gcdr a b == 0) = (a == 0) && (b == 0).
Proof. by rewrite -!dvd0r dvdr_gcd. Qed.

Hint Resolve dvdr_gcdr dvdr_gcdl : core.

Lemma gcdr_def : forall x a b, x %| a -> x %| b ->
  (forall x', x' %| a -> x' %| b -> (x' %| x)) -> gcdr a b %= x.
Proof. by move=> x a b xa xb hx; rewrite eqd_def dvdr_gcd xa xb hx. Qed.

Lemma gcdrC a b : gcdr a b %= gcdr b a.
Proof. by rewrite /eqd ?dvdr_gcd ?dvdr_gcdr ?dvdr_gcdl. Qed.

Hint Resolve gcdrC : core.

Lemma eqd_gcd c d a b : a %= c -> b %= d -> gcdr a b %= gcdr c d.
Proof.
move=> ac bd; rewrite eqd_def !dvdr_gcd -(eqd_dvd (eqdd _) ac) dvdr_gcdl.
rewrite -(eqd_dvd (eqdd _) bd) dvdr_gcdr (eqd_dvd (eqdd _) ac) dvdr_gcdl.
by rewrite (eqd_dvd (eqdd _) bd) dvdr_gcdr.
Qed.

(* Lemma gcdq0r : forall x : DR, gcdqr (\pi 0) x = x. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcd0r _)). Qed. *)

(* Local Notation DR := {R %/ %=R}. *)

(* Lemma gcdqr_pi : forall a b, gcdqr (\pi a) (\pi b) = \pi (gcdr a b). *)
(* Proof. *)
(* move=> a b /=; rewrite /gcdqr. *)
(* rewrite (equivP (@eqd_gcdr a _ _ _)) ?equivE ?reprK //. *)
(* by rewrite (equivP (@eqd_gcdl b _ _ _)) ?equivE ?reprK. *)
(* Qed. *)

Lemma gcd0r a : gcdr 0 a %= a.
Proof. by rewrite /eqd dvdr_gcd dvdr0 dvdrr !andbT. Qed.

(* Lemma gcdq0r : forall x : DR, gcdqr (\pi 0) x = x. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcd0r _)). Qed. *)

Lemma gcdr0 a : gcdr a 0 %= a.
Proof. by rewrite /eqd dvdr_gcd dvdr0 dvdrr !andbT. Qed.

(* Lemma gcdqr0 : forall x : DR, gcdqr x (\pi 0) = x. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcdr0 _)). Qed. *)

Lemma gcd1r a : gcdr 1 a %= 1.
Proof. by rewrite /eqd dvdr_gcd dvdrr dvd1r !andbT. Qed.

(* Lemma gcdq1r : forall x : DR, gcdqr (\pi 1) x = \pi 1. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcd1r _)). Qed. *)

Lemma gcdr1 a : gcdr a 1 %= 1.
Proof. by rewrite /eqd dvdr_gcd dvdrr dvd1r !andbT. Qed.

(* Lemma gcdqr1 : forall x : DR, gcdqr x (\pi 1) = \pi 1. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcdr1 _)). Qed. *)

Lemma gcdrA a b c : gcdr a (gcdr b c) %= gcdr (gcdr a b) c.
Proof.
rewrite /eqd !dvdr_gcd !dvdr_gcdl !dvdr_gcdr.
do 2!rewrite (dvdr_trans (dvdr_gcdr _ _)) //.
by do 2!rewrite (dvdr_trans (dvdr_gcdl _ _)) //.
Qed.

(* Lemma gcdqrA : forall x y z : DR, gcdqr x (gcdqr y z) = gcdqr (gcdqr x y) z. *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y; elim/quotW=> z. *)
(* by rewrite !gcdqr_pi (equivP (gcdrA _ _ _)) -!gcdqr_pi !reprK. *)
(* Qed. *)

(* Lemma gcdqrC : forall x y : DR, gcdqr x y = gcdqr y x. *)
(* Proof. *)
(* by elim/quotW=> x; elim/quotW=> y; rewrite /gcdqr (equivP (gcdrC _ _)). *)
(* Qed. *)

(* Lemma gcdqrCA : forall x y z : DR, gcdqr x (gcdqr y z) = gcdqr y (gcdqr x z). *)
(* Proof. by move=> x y z; rewrite !gcdqrA [gcdqr x _]gcdqrC. Qed. *)

Lemma gcdrCA a b c : gcdr a (gcdr b c) %= gcdr b (gcdr a c).
Proof.
rewrite (eqd_trans (gcdrA _ _ _)) // eqd_sym (eqd_trans (gcdrA _ _ _)) //.
by rewrite (eqd_gcd (gcdrC _ _)) //.
Qed.
(*
Proof.
move=> a b c; apply/equivP; rewrite !(equivP (gcdrA _ _ _)); apply/equivP=> /=.
by rewrite (eqd_gcd (gcdrC _ _) (eqdd _)).
Qed.
*)

(* Lemma gcdqrAC : forall x y z : DR, gcdqr (gcdqr x y) z = gcdqr (gcdqr x z) y. *)
(* Proof. by move=> x y z; rewrite -!gcdqrA [gcdqr y _]gcdqrC. Qed. *)

Lemma gcdrAC a b c : gcdr (gcdr a b) c %= gcdr (gcdr a c) b.
Proof.
rewrite (eqd_trans _ (gcdrA _ _ _)) // eqd_sym (eqd_trans _ (gcdrA _ _ _)) //.
by rewrite (eqd_gcd _ (gcdrC _ _)) //.
Qed.
(*
Proof.
move=> a b c; apply/equivP; rewrite -!(equivP (gcdrA _ _ _)); apply/equivP=> /=.
by rewrite (eqd_gcd (eqdd _) (gcdrC _ _)).
Qed.
*)

Lemma gcdr_mul2r a b c : gcdr (a * c) (b * c) %= gcdr a b * c.
Proof.
rewrite /eqd !dvdr_gcd !dvdr_mul // !andbT.
case c0: (c == 0); first by rewrite (eqP c0) !mulr0 dvdr0.
have Hc: c %| gcdr (a * c) (b * c) by rewrite dvdr_gcd !dvdr_mull //.
case/dvdrP: Hc=> g Hg.
rewrite Hg dvdr_mul // dvdr_gcd -![g %| _](@dvdr_mul2r _ c) ?c0 //.
by rewrite -Hg dvdr_gcdl dvdr_gcdr.
Qed.

(* Lemma gcdqr_mul2r : forall x y z : DR, gcdqr (x *d z) (y *d z) = gcdqr x y *d z. *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y; elim/quotW=> z. *)
(* by rewrite 2!mulqr_pi 2!gcdqr_pi mulqr_pi (equivP (gcdr_mul2r _ _ _)). *)
(* Qed. *)

Lemma gcdr_mul2l a b c : gcdr (c * a) (c * b) %= c * gcdr a b.
Proof. by rewrite ![c * _]mulrC gcdr_mul2r. Qed.

(* Lemma gcdqr_mul2l : forall x y z : DR, gcdqr (z *d x) (z *d y) = z *d gcdqr x y. *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y; elim/quotW=> z. *)
(* by rewrite 2!mulqr_pi 2!gcdqr_pi mulqr_pi (equivP (gcdr_mul2l _ _ _)). *)
(* Qed. *)

Lemma mulr_gcdr a b c : a * gcdr b c %= gcdr (a * b) (a * c).
Proof. by rewrite eqd_sym gcdr_mul2l. Qed.

Lemma mulr_gcdl a b c : gcdr a b * c %= gcdr (a * c) (b * c).
Proof. by rewrite eqd_sym gcdr_mul2r. Qed.

(* Lemma mulqr_gcdr : forall x y z : DR, gcdqr x y *d z = gcdqr (x *d z) (y *d z). *)
(* Proof. by move=> x y z; rewrite gcdqr_mul2r. Qed. *)

(* Lemma mulqr_gcdl : forall x y z : DR, z *d gcdqr x y = gcdqr (z *d x) (z *d y). *)
(* Proof. by move=> x y z; rewrite gcdqr_mul2l. Qed. *)

(* *)
(* Lemma gcdr_mul : forall a b c g, gcdr a b %= g -> gcdr (c * a) (c * b) %= c * g. *)
(* Proof. *)
(* move=> a b c g. *)
(* rewrite /eqd !dvdr_gcd; case/and3P=> hg ha hb. *)
(* rewrite !dvdr_mul2lW //. *)

(* case Hc: (c == 0); first by move: (eqP Hc)-> => _; rewrite !mul0r gcdr0. *)
(* case Hg: (g == 0). *)
(*   move: (eqP Hg)->. *)
(*   case/gcdrP=> a0 [b0] _; move: (dvd0r a0)->; move: (dvd0r b0)->. *)
(*   by rewrite mulr0 gcdr0. *)
(* case/gcdrP=> ga [gb] H. *)
(* have Hcg: c*g %| gcdr (c*a) (c*b) by rewrite dvdr_gcd ?dvdr_mul. *)
(* case/dvdrP: Hcg=> x Hcgx. *)
(* have Ha: g*x %| a. *)
(*   by rewrite (@dvdr_cancel (g*x) a c) //; first exact: (negbT Hc); *)
(*   rewrite mulrA -Hcgx dvdr_gcdl. *)
(* have Hb: g*x %| b *)
(*   by rewrite (@dvdr_cancel (g*x) b c) //; first exact: (negbT Hc); *)
(*   rewrite mulrA -Hcgx dvdr_gcdr. *)
(* exact: (eqd_mulUr (eq_eqd Hcgx) (dvdr_mulrU (negbT Hg) (H _ _ _))). *)
(* Qed. *)
(* *)

Lemma gcdr_addr_r c a b : a %| b -> gcdr a (c + b) %= gcdr a c.
Proof.
move=> hab.
rewrite /eqd !dvdr_gcd !dvdr_gcdl dvdr_add ?(dvdr_trans _ hab) //.
by rewrite -{2}[c](@addrK _ b) dvdr_sub // (dvdr_trans _ hab).
Qed.

Lemma gcdr_addl_r c a b : a %| b -> gcdr a (b + c) %= gcdr a c.
Proof. by move=> hab; rewrite addrC gcdr_addr_r. Qed.

Lemma gcdr_addr_l a b c : b %| c -> gcdr (a + c) b %= gcdr a b.
Proof.
move=> Hbc.
by rewrite (eqd_trans (gcdrC _ _)) ?(eqd_trans (gcdr_addr_r _ _)).
Qed.

Lemma gcdr_addl_l a b c : b %| c -> gcdr (c + a) b %= gcdr a b.
Proof.
move=> Hbc.
by rewrite (eqd_trans (gcdrC _ _)) ?(eqd_trans (gcdr_addl_r _ _)).
Qed.

Lemma gcdr_addl_mul a b m : gcdr a (a * m + b) %= gcdr a b.
Proof. by rewrite gcdr_addl_r // dvdr_mulr. Qed.

(* lcm *)

Lemma dvdr_gcd_mul a b : gcdr a b %| a * b.
Proof. by rewrite dvdr_mull. Qed.

Lemma mulr_lcm_gcd a b : lcmr a b * gcdr a b = a * b.
Proof.
rewrite /lcmr /=; move: (dvdr_gcd_mul a b).
have [-> | a0] := eqVneq a 0; first by rewrite !mul0r.
have [-> | b0] := eqVneq b 0; first by rewrite !(mulr0, mul0r).
by rewrite /dvdr; case: odivrP => // x.
Qed.

Lemma lcmr0 a : lcmr a 0 = 0.
Proof. by rewrite /lcmr /= eqxx orbT. Qed.

Lemma lcm0r a : lcmr 0 a = 0.
Proof. by rewrite /lcmr eqxx. Qed.

Lemma dvdr_lcm a b c : (lcmr a b %| c) = (a %| c) && (b %| c) :> bool.
Proof.
have [-> | a0] := eqVneq a 0.
  rewrite lcm0r dvd0r.
  by case: eqP => //= ->; rewrite dvdr0.
have [-> | b0] := eqVneq b 0.
  rewrite lcmr0 dvd0r andbC.
  by case: eqP => //= ->; rewrite dvdr0.
rewrite -(@dvdr_mul2r _ (gcdr a b)); last by rewrite gcdr_eq0 negb_and a0.
rewrite mulr_lcm_gcd (eqd_dvd (eqdd _) (mulr_gcdr _ _ _)) dvdr_gcd {1}mulrC.
by rewrite !dvdr_mul2r // andbC.
Qed.

Lemma dvdr_lcml a b : a %| lcmr a b.
Proof. by move: (dvdrr (lcmr a b)); rewrite dvdr_lcm; case/andP. Qed.

Hint Resolve dvdr_lcml : core.

Lemma dvdr_lcmr a b : b %| lcmr a b.
Proof. by move: (dvdrr (lcmr a b)); rewrite dvdr_lcm; case/andP. Qed.

Hint Resolve dvdr_lcmr : core.

Lemma dvdr_gcdr_lcmr a b : gcdr a b %| lcmr a b.
Proof. exact: (dvdr_trans (dvdr_gcdl a b) (dvdr_lcml a b)). Qed.

Lemma lcm1r a : lcmr 1 a %= a.
Proof. by rewrite /eqd dvdr_lcm dvdr_lcmr dvdrr dvd1r !andbT. Qed.

Lemma lcmr1 a : lcmr a 1 %= a.
Proof. by rewrite /eqd dvdr_lcm dvdr_lcml dvdrr dvd1r !andbT. Qed.

Lemma lcmrC a b : lcmr a b %= lcmr b a.
Proof.
case/boolP: (gcdr b a == 0) => [|H0].
  by rewrite gcdr_eq0; case/andP => /eqP-> _; rewrite lcmr0 lcm0r.
rewrite -(@eqd_mul2r _ (gcdr b a)) //.
by rewrite (eqd_trans (eqd_mul (eqdd _) (gcdrC b a))) // !mulr_lcm_gcd mulrC.
Qed.

Lemma lcmrA a b c : lcmr a (lcmr b c) %= lcmr (lcmr a b) c.
Proof.
rewrite /eqd !dvdr_lcm !dvdr_lcml !dvdr_lcmr.
rewrite 2!(dvdr_trans _ (dvdr_lcml _ _)) //.
by do 2!rewrite (dvdr_trans _ (dvdr_lcmr _ _)) //.
Qed.

Lemma eqd_lcmr a b c : a %= b -> lcmr a c %= lcmr b c.
Proof.
move=> Hab.
rewrite /eqd !dvdr_lcm !dvdr_lcmr (eqd_dvd Hab (eqdd _)).
by rewrite dvdr_lcml -(eqd_dvd Hab (eqdd _)) dvdr_lcml.
Qed.

Lemma eqd_lcml a b c : a %= b -> lcmr c a %= lcmr c b.
Proof.
move=> Hab.
rewrite (eqd_trans (lcmrC _ _)) // (eqd_trans _ (lcmrC _ _)) //.
by rewrite eqd_lcmr // eqd_sym.
Qed.

Lemma lcmrCA a b c : lcmr a (lcmr b c) %= lcmr b (lcmr a c).
Proof.
rewrite (eqd_trans (lcmrA _ _ _)) //.
by rewrite (eqd_trans (eqd_lcmr _ (lcmrC _ _))) // eqd_sym lcmrA.
Qed.

Lemma lcmrAC a b c : lcmr (lcmr a b) c %= lcmr (lcmr a c) b.
Proof.
rewrite (eqd_trans _ (lcmrA _ _ _)) //.
by rewrite (eqd_trans _ (eqd_lcml _ (lcmrC _ _))) // eqd_sym lcmrA.
Qed.

Lemma mulr_lcmr a b c : a * lcmr b c %= lcmr (a * b) (a * c).
Proof.
case/boolP: ((a * b == 0) && (a * c == 0)) => [/andP[] | H0].
  rewrite mulf_eq0; case/orP => /eqP->.
    by rewrite !mul0r lcm0r.
  by rewrite mulr0 !lcm0r mulr0.
rewrite -(@eqd_mul2r _ (gcdr (a * b) (a * c))) ?gcdr_eq0 // mulr_lcm_gcd.
rewrite eqd_sym (eqd_trans _ (eqd_mul (eqdd _) (mulr_gcdr a b c))) //.
by rewrite -!mulrA [lcmr b c * _]mulrCA mulr_lcm_gcd [b * _]mulrCA.
Qed.

Lemma mulr_lcml a b c : lcmr a b * c %= lcmr (a * c) (b * c).
Proof. by rewrite ![_ * c]mulrC mulr_lcmr. Qed.

Lemma lcmr_mul2r a b c : lcmr (a * c) (b * c) %= lcmr a b * c.
Proof. by rewrite eqd_sym mulr_lcml. Qed.

Lemma lcmr_mul2l a b c : lcmr (c * a) (c * b) %= c * lcmr a b.
Proof. by rewrite ![c * _]mulrC lcmr_mul2r. Qed.

Lemma lcmr_mull a b : lcmr a (a * b) %= a * b.
Proof.
have [-> | a0] := eqVneq a 0; first by rewrite mul0r /eqd !lcm0r dvdr0.
rewrite -{1}[a]mulr1 (eqd_trans (lcmr_mul2l 1 b a)) // eqd_mul2l //.
exact: (lcm1r b).
Qed.

Lemma lcmr_mulr a b : lcmr b (a * b) %= a * b.
Proof. by rewrite mulrC lcmr_mull. Qed.

Lemma dvdr_lcm_idr a b : a %| b -> lcmr a b %= b.
Proof. by case/dvdrP=>x ->; rewrite lcmr_mulr. Qed.

Lemma dvdr_lcm_idl a b : b %| a -> lcmr a b %= a.
Proof. by case/dvdrP=> x ->; rewrite (eqd_trans (lcmrC _ _)) // lcmr_mulr. Qed.

(** gcdsr and lcmsr *)
Lemma gcdsr0 : (@gcdsr R) [::] = 0.
Proof. by []. Qed.

Lemma gcdsr_cons : forall a s, gcdsr (a :: s) = gcdr a (gcdsr s).
Proof. by []. Qed.

Lemma dvdr_gcds : forall (l : seq R) (g : R), g %| gcdsr l = all (%|%R g) l.
Proof. by elim=> [|a l ihl] g; rewrite /= ?dvdr0 // dvdr_gcd ihl. Qed.

Lemma dvdr_mem_gcds (l : seq R) x : x \in l -> gcdsr l %| x.
Proof.
by move=> hx; move: (dvdrr (gcdsr l)); rewrite dvdr_gcds; move/allP; apply.
Qed.

Lemma lcmsr0 : (@lcmsr R) [::] = 1.
Proof. by []. Qed.

Lemma lcmsr_cons : forall a s, lcmsr (a :: s) = lcmr a (lcmsr s).
Proof. by []. Qed.

Lemma dvdr_lcms : forall (l : seq R) (m : R), lcmsr l %| m = all (%|%R^~ m) l.
Proof. by elim=> [|a l ihl] m; rewrite /= ?dvd1r // dvdr_lcm ihl. Qed.

Lemma dvdr_mem_lcms (l : seq R) x : x \in l -> x %| lcmsr l.
Proof.
by move=> hx; move: (dvdrr (lcmsr l)); rewrite dvdr_lcms; move/allP; apply.
Qed.

(* Coprimality *)
Definition coprimer a b := gcdr a b %= 1.

Lemma coprimer_sym a b : coprimer a b = coprimer b a.
Proof. by rewrite /coprimer; apply: congr_eqd. Qed.

Lemma euclid_inv a b c : coprimer a b -> (a * b %| c) = (a %| c) && (b %| c).
Proof.
move=> cab.
by rewrite -mulr_lcm_gcd (eqd_dvd (eqd_mul (eqdd _) cab) (eqdd _)) mulr1 dvdr_lcm.
Qed.

Lemma euclid b a c : coprimer a b -> (a %| c * b) = (a %| c) :> bool.
Proof.
move=> cab; symmetry.
rewrite -{1}[c]mulr1 -(eqd_dvd (eqdd _) (eqd_mul (eqdd c) cab)).
by rewrite (eqd_dvd (eqdd _) (mulr_gcdr _ _ _)) dvdr_gcd dvdr_mull.
Qed.

Lemma euclid_gcdr a b c : coprimer a b -> gcdr a (c * b) %= gcdr a c.
Proof.
move=> cab.
rewrite eqd_def !dvdr_gcd !dvdr_gcdl /= andbC dvdr_mulr //= -(@euclid b) //.
rewrite /coprimer (eqd_trans (gcdrAC _ _ _)) //.
by rewrite (eqd_trans (eqd_gcd cab (eqdd _))) ?gcd1r.
Qed.

Lemma euclid_gcdl a b c : coprimer a b -> gcdr a (b * c) %= gcdr a c.
Proof. by move=> cab; rewrite mulrC euclid_gcdr. Qed.

Lemma coprimer_mulr a b c : coprimer a (b * c) = coprimer a b && coprimer a c.
Proof.
case/boolP: (coprimer a b) => co_pm /=.
  by rewrite /coprimer; apply: congr_eqd; rewrite // euclid_gcdl.
apply: contraNF co_pm=> cabc.
apply: gcdr_def; rewrite ?dvd1r // => x xa xb.
by rewrite -(eqd_dvd (eqdd _) cabc) dvdr_gcd xa dvdr_mulr.
Qed.

Lemma coprimer_mull a b c : coprimer (b * c) a = coprimer b a && coprimer c a.
Proof. by rewrite !(coprimer_sym _ a) coprimer_mulr. Qed.

Lemma coprimer_dvdl a b c : a %| b -> coprimer b c -> coprimer a c.
Proof.
move=> dvd_ab cbc; apply: gcdr_def; rewrite ?dvd1r //= => d da dc.
by rewrite -(eqd_dvdr _ cbc) dvdr_gcd (dvdr_trans da).
Qed.

Lemma coprimer_dvdr a b c : a %| b -> coprimer c b -> coprimer c a.
Proof.
move=> dvd_ab cbc; apply: gcdr_def; rewrite ?dvd1r //= => d dc da.
by rewrite -(eqd_dvdr _ cbc) dvdr_gcd andbC (dvdr_trans da).
Qed.

Lemma coprimer_expl k a b : coprimer a b -> coprimer (a ^+ k) b.
Proof.
move=> cab; elim: k=> [|k ihk]; first by rewrite /coprimer gcd1r.
by rewrite exprSr coprimer_mull ihk cab.
Qed.

Lemma coprimer_expr k a b : coprimer a b -> coprimer a (b ^+ k).
Proof.
move=> cab; elim: k=> [|k ihk]; first by rewrite /coprimer gcdr1.
by rewrite exprSr coprimer_mulr ihk cab.
Qed.

Lemma coprimer_pexpl k a b : 0 < k -> coprimer (a ^+ k) b = coprimer a b.
Proof.
case: k => [|k] // _; apply/idP/idP; last by apply: coprimer_expl.
by apply: coprimer_dvdl; rewrite exprS dvdr_mulr.
Qed.

Lemma coprimer_pexpr k a b : 0 < k -> coprimer a (b ^+ k) = coprimer a b.
Proof.
case: k => [|k] // _; apply/idP/idP; last by apply: coprimer_expr.
by apply: coprimer_dvdr; rewrite exprS dvdr_mulr.
Qed.

Lemma dvdr_coprime a b : a %| b -> coprimer a b -> a %= 1.
Proof.
move=> ab cab; rewrite -(eqd_rtrans cab) eqd_def dvdr_gcdl andbT.
by rewrite dvdr_gcd dvdrr.
Qed.

(** Irreducible and prime elements *)

Definition primer a := ((a == 0 = false)
                      * (a %= 1 = false)
                      * (forall b c, a %| (b * c) = (a %| b) || (a %| c) :> bool)%R)%type.

Definition irredr a := ((a == 0 = false)
                      * (a %= 1 = false)
                      * (forall b c, a %= b * c -> (b %= 1) || (c %= 1))%R)%type.

Lemma irredrP : forall a, irredr a ->
  forall b c, a %= b * c -> b %= 1 \/ c %= 1.
Proof. by move=> ? [ha ia] *; apply/orP; rewrite ia. Qed.

Lemma irredr_dvd : forall a b, irredr a -> a %| b = ~~(coprimer a b) :> bool.
Proof.
rewrite /coprimer=> a b ia; case g1: (_ %= 1)=> /=.
  apply/negP=> hab; suff: a %= 1 by rewrite ia.
  by rewrite -dvdr1 (@dvdr_trans _ (gcdr a b)) ?dvdr_gcd ?dvdrr // dvdr1.
case: (dvdrP _ _ (dvdr_gcdl a b))=> x hx; rewrite hx.
move/eq_eqd: hx; case/irredrP => //; last by rewrite g1.
move=> hx; rewrite (eqd_dvd (eqd_mul hx (eqdd _)) (eqdd _)).
by rewrite mul1r dvdr_gcdr.
Qed.

Lemma irredr_coprimer : forall a b, irredr a -> coprimer a b = ~~(a %| b).
Proof. by move=> a b ia; rewrite irredr_dvd // negbK. Qed.

Lemma irredr_primer : forall a, irredr a <-> primer a.
Proof.
move=> a; split=> ia; rewrite /primer /irredr !ia; do ![split]=> b c.
  apply/idP/idP; last by case/orP=> ha; [rewrite dvdr_mulr|rewrite dvdr_mull].
  rewrite [_ %| b]irredr_dvd //; case cab: (coprimer _ _)=> //=.
  by rewrite mulrC euclid.
have [-> | b0] := eqVneq b 0; first by rewrite mul0r eqdr0 ia.
have [-> | c0] := eqVneq c 0; first by rewrite mulr0 eqdr0 ia.
rewrite eqd_def ia andb_orl.
case/orP; case/andP; move/(dvdr_trans _)=> h; move/h.
  by rewrite dvdr_mull_l // => ->; rewrite orbT.
by rewrite dvdr_mulr_l // => ->.
Qed.

(** bigop **)

Lemma big_dvdr_gcdr (I : finType) (F : I -> R) :
   forall i, \big[(@gcdr R)/0]_i F i %| F i.
Proof.
move=> i; elim: (index_enum I) (mem_index_enum i)=> // a l IHl.
rewrite in_cons big_cons =>/orP [/eqP ->|H].
  by rewrite dvdr_gcdl.
exact: (dvdr_trans (dvdr_gcdr _ _) (IHl H)).
Qed.

Lemma big_gcdrP (I : finType) (F : I -> R) d :
  (forall i, d %| F i) -> d %| \big[(@gcdr R)/0]_(i : I) F i.
Proof.
move=> Hd ; elim: (index_enum I)=> [|a l IHl].
  by rewrite big_nil dvdr0.
rewrite big_cons dvdr_gcd.
by apply/andP; split; [apply: Hd | apply: IHl].
Qed.

Lemma big_gcdr_def (I : finType) (F : I -> R) d :
  (exists k, F k %| d) -> \big[(@gcdr R)/0]_(i : I) F i %| d.
Proof.
by case=> k; apply: dvdr_trans; apply: big_dvdr_gcdr.
Qed.
(****)

End GCDDomainTheory.

Module BezoutDomain.

Variant bezout_spec (R : gcdDomainType) (a b : R) : R * R -> Type:=
  BezoutSpec x y of gcdr a b %= x * a + y * b : bezout_spec a b (x, y).

Record mixin_of (R : gcdDomainType) : Type := Mixin {
  bezout : R -> R -> (R * R);
   _ : forall a b, bezout_spec a b (bezout a b)
}.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : GcdDomain.class_of R;
  mixin : mixin_of (GcdDomain.Pack base)
}.
Local Coercion base : class_of >-> GcdDomain.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@GcdDomain.Pack T b0)) :=
  fun bT b & phant_id (GcdDomain.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m).

Definition eqType := Equality.Pack class.
Definition choiceType := Choice.Pack class.
Definition zmodType := GRing.Zmodule.Pack class.
Definition ringType := GRing.Ring.Pack class.
Definition comRingType := GRing.ComRing.Pack class.
Definition unitRingType := GRing.UnitRing.Pack class.
Definition comUnitRingType := GRing.ComUnitRing.Pack class.
Definition idomainType := GRing.IntegralDomain.Pack class.
Definition dvdRingType := DvdRing.Pack class.
Definition gcdDomainType := GcdDomain.Pack class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GcdDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion dvdRingType : type >-> DvdRing.type.
Canonical Structure dvdRingType.
Coercion gcdDomainType : type >-> GcdDomain.type.
Canonical Structure gcdDomainType.
Notation bezoutDomainType := type.
Notation BezoutDomainType T m := (@pack T _ m _ _ id _ id).
Notation BezoutDomainMixin := Mixin.
Notation "[ 'bezoutDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'bezoutDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'bezoutDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'bezoutDomainType'  'of'  T ]") : form_scope.
End Exports.

End BezoutDomain.
Export BezoutDomain.Exports.

Definition bezout R := BezoutDomain.bezout (BezoutDomain.class R).

Section BezoutDomainTheory.

Variable R : bezoutDomainType.

Implicit Types a b : R.

(* Lemma bezout_gcdPlr : forall a b, GCDDomain.gcdP a b (bezout a b).1. *)
(* Proof. by case: R => [? [? []]]. Qed. *)

Lemma bezoutP : forall a b, BezoutDomain.bezout_spec a b (bezout a b).
Proof. by case: R=> [? [? []]]. Qed.

Definition egcdr a b :=
  let: (u, v) := bezout a b in
  let g := u * a + v * b in
  if g == 0 then (0,1,0,1,0) else
    let a1 := odflt 0 (a %/? g) in
    let b1 := odflt 0 (b %/? g) in
    (g, u, v, a1, b1).

Variant egcdr_spec a b : R * R * R * R * R -> Type :=
  EgcdrSpec g u v a1 b1 of u * a1 + v * b1 = 1
                         & g %= gcdr a b
                         & a = a1 * g
                         & b = b1 * g : egcdr_spec a b (g, u, v, a1, b1).

Lemma egcdrP a b : egcdr_spec a b (egcdr a b).
Proof.
rewrite /egcdr; case: bezoutP=> x y hg /=.
move: (dvdr_gcdr a b) (dvdr_gcdl a b); rewrite !(eqd_dvd hg (eqdd _))=> ha hb.
have [g_eq0 | g_neq0] := boolP (_ == 0).
  rewrite (eqP g_eq0) eqdr0 in hg.
  move: (hg); rewrite gcdr_eq0=> /andP[/eqP-> /eqP->].
  constructor; do ?by rewrite mulr0.
    by rewrite mulr0 addr0 mulr1.
  by rewrite eqd_sym gcdr0.
constructor.
move: hb ha.
rewrite /dvdr.
case: odivrP=> //= a1 Ha _.
case: odivrP=> //= b1 Hb _.
- apply/(mulIf g_neq0).
  by rewrite mulrDl mul1r -!mulrA -Ha -Hb.
- by rewrite eqd_sym.
- by move: hb; rewrite /dvdr; case: odivrP.
by move: ha; rewrite /dvdr; case: odivrP.
Qed.

(* Proof that any finitely generated ideal is principal *)
(* This could use gcdsr if it would be expressed using bigops... *)
Fixpoint principal_gen n : 'cV[R]_n -> R :=
  if n is p.+1 then
    fun I : 'cV[R]_(1 + p) =>
      let x := I 0 0 in
      let y := principal_gen (dsubmx I) in
      let: (g,_,_,_,_) := egcdr x y in g
  else fun => 0.

(* Fixpoint principal_gen n (r : 'rV[R]_n) : R := \big[(fun x y => (egcdr x y).1.1.1.1) /0]_(i < n) (r 0 i). *)

Lemma principal_gen_dvd : forall n (I : 'cV[R]_n) i, principal_gen I %| I i 0.
Proof.
elim => [I i| n ih]; first by rewrite flatmx0 /= !mxE dvdrr.
rewrite [n.+1]/(1 + n)%nat => I i.
rewrite -[I]vsubmxK !mxE.
case: splitP => j hj /=.
  rewrite !ord1 !mxE /=.
  case: splitP => // j' _.
  rewrite ord1 mxE lshift0.
  case: egcdrP => g u v a b _.
  rewrite eqd_def; case/andP => h _ _ _.
  exact: (dvdr_trans h (dvdr_gcdl _ _)).
case: egcdrP => g u v a b _.
rewrite eqd_def col_mxKd; case/andP => h _ _ _.
apply/(dvdr_trans (dvdr_trans h (dvdr_gcdr _ _))).
by rewrite ih.
Qed.

Definition principal n (I : 'cV[R]_n) : 'M[R]_1 := (principal_gen I)%:M.

(* (x) \subset (x1...xn) iff exists (v1...vn) such that (x1...xn)(v1...vn)^T = (x) *)
Fixpoint principal_w1 n : 'cV[R]_n -> 'rV[R]_n :=
  if n is p.+1 then
    fun (I : 'cV[R]_(1 + p)) =>
      let g := principal_gen (dsubmx I) in
      let us := principal_w1 (dsubmx I) in
      let: (g',u,v,a1,b1) := egcdr (I 0 0) g in
      row_mx u%:M (v *: us)
  else fun => 0.

Lemma principal_w1_correct : forall n (I : 'cV[R]_n),
  principal_w1 I *m I = principal I.
Proof.
elim => [I | n ih]; first by rewrite flatmx0 mulmx0 /principal rmorph0.
rewrite [n.+1]/(1 + n)%nat => I.
rewrite -[I]vsubmxK /principal /= col_mxKd {-2}vsubmxK.
case: egcdrP => g u v a1 b1 hbezout _ h1 h2 /=.
rewrite [row_mx u%:M _ *m _]mul_row_col -scalemxAl ih /principal h2.
have -> : usubmx I = (I 0 0)%:M.
  apply/matrixP => i j.
   by rewrite !mxE !ord1 eqxx /= mulr1n lshift0.
rewrite h1 !scalar_mxM -mul_scalar_mx !mulmxA -mulmxDl -!scalar_mxM -rmorphD.
by rewrite hbezout mul1mx.
Qed.

(* (x1...xn) \subset (x) iff exists (w1...wn) such that (x)(w1...wn) = (x1...xn) *)
Definition principal_w2 n (I : 'cV[R]_n) : 'cV[R]_n :=
  let g := principal_gen I in
  map_mx (fun x => odflt 0 (x %/? g)) I.

Lemma principal_w2_correct : forall n (I : 'cV[R]_n),
  principal_w2 I *m principal I = I.
Proof.
move=> n I.
rewrite mul_mx_scalar.
apply/matrixP => i j; rewrite !mxE !ord1 /= {j}.
case: n I i => [|n] I i; first by rewrite !flatmx0 /= mul0r !mxE.
case: odivrP => [x -> | H]; first by rewrite mulrC.
case/dvdrP: (principal_gen_dvd I i)=> x Hx.
move: (H x).
by rewrite Hx eqxx.
Qed.

(* Bezout matrices *)
Section Bezout_mx.

(*****************
  if the following Bezout identity holds: u * a1 + v * b1 = 1,
  Bezout_mx a b n k represents the following matrix (dots are zeros):

          (kth column)
  / u .... v ..... \
  | . 1 .......... |
  | ....1......... |
  | -b1 .. a1 .... | (kth row)
  | ..........1... |
  \ .............1 /


  (determinant is +/-1)
******************)

Definition combine_mx (a b c d : R) (m : nat) (k : 'I_m) :=
  let k' := lift 0 k in
  let d := \row_j (a *+ (j == 0) + d *+ (j == k') + ((j != 0) && (j != k'))%:R) in
  diag_mx d + c *: delta_mx k' 0 + b *: delta_mx 0 k'.

Definition combine_step (a b c d : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :=
  let k' := lift 0 k in
  let r0 := a *: row 0 M + b *: row k' M in
  let rk := c *: row 0 M + d *: row k' M in
  \matrix_i (r0 *+ (i == 0) + rk *+ (i == k') + row i M *+ ((i != 0) && (i != k'))).

Definition Bezout_mx (a b : R) (m : nat) (k : 'I_m) :=
  let:(_,u,v,a1,b1) := egcdr a b in combine_mx u v (-b1) a1 k.

Definition Bezout_step (a b : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :=
  let:(_,u,v,a1,b1) := egcdr a b in combine_step u v (-b1) a1 M k.

Lemma combine_stepE (a b c d : R) (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
  combine_step a b c d M k = combine_mx a b c d k *m M.
Proof.
apply/matrixP=> i j; have [g u v a' b' _ _ _ _] := egcdrP a b.
rewrite !mxE (bigD1 ord0) // !mxE (bigD1 (lift 0 k)) // !mxE /=.
case H: (i == 0).
  rewrite big1=> [|l /andP [/negbTE H1 /negbTE H2]].
    by rewrite (eqP H) !eqxx !mulr1n !mxE !mulr0 !addr0 mulr0n add0r mulr1.
  by rewrite !mxE (eqP H) (eq_sym 0 l) H1 H2 mulr0n !mulr0 !add0r mul0r.
case H': (i == lift 0 k).
  rewrite big1=> [|l /andP [/negbTE H1 /negbTE H2]].
    by rewrite (eqP H') !(eqxx,mulr1n,mxE,mulr0,addr0,mulr1,mulr0n,add0r).
  by rewrite !mxE (eqP H') !(eq_sym _ l) eqxx H1 H2 mulr0n !mulr0 !add0r mul0r.
rewrite (bigD1 i); last by rewrite H H'.
rewrite !mxE big1=> [/=|l /andP [/andP [/negbTE H1 /negbTE H2] /negbTE H3]].
  by rewrite H H' eqxx !(mulr0n,mulr0,mulr1n,addr0,mul0r,add0r,mul1r).
by rewrite !mxE H H' H1 H2 (eq_sym i l) H3 mulr0n !mulr0 !addr0 mul0r.
Qed.

Lemma combine_mx_inv (a b c d : R) m (k : 'I_m) :
  a * d - b * c = 1 ->
  combine_mx a b c d k *m combine_mx d (-b) (-c) a k = 1%:M.
Proof.
move=> H; rewrite -combine_stepE; apply/matrixP=> i j; rewrite !mxE.
case Hi: (i == 0).
  rewrite !mxE (eqP Hi) !eqxx !mulr0 mxE !addr0 (eq_sym 0 j).
  case Hj: (j == 0); first by rewrite (eqP Hj) mulr1 !mulr0 addr0 sub0r mulrN.
  rewrite !mulr0 !add0r addr0 (eq_sym _ j).
  case: (j == lift 0 k); last by rewrite !mulr0 add0r.
  by rewrite mulr1 mulr1n mulrN mulrC addNr.
case Hj: (j == 0).
  rewrite !mxE (eqP Hj) Hi add0r.
  case Hk: (i == _); last by rewrite !mxE Hi Hk eqxx !add0r !mulr0 addr0.
  by rewrite !mxE !eqxx !mulr0 mulr1 !addr0 !add0r mulrN addrC mulrC addNr.
case Hk: (i == _); last by rewrite !mxE Hi Hj Hk !mulr0 !add0r !addr0.
rewrite !mxE (eq_sym 0 j) Hj (eqP Hk) !(eqxx,mulr0,addr0,add0r) (eq_sym _ j).
case: (j == lift 0 k); last by rewrite !mulr0 addr0.
by rewrite !mulr1 addrC mulrN (mulrC c) (mulrC d).
Qed.

Lemma Bezout_stepE a b (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
  Bezout_step a b M k = Bezout_mx a b k *m M.
Proof.
rewrite /Bezout_step /Bezout_mx; have [g u v a' b' _ _ _ _] := egcdrP.
by rewrite combine_stepE.
Qed.

Lemma Bezout_step_mx00 m n (M : 'M_(1 + m,1 + n)) {k : 'I_m} :
 (Bezout_step (M 0 0) (M (lift 0 k) 0) M k) 0 0 %= gcdr (M 0 0) (M (lift 0 k) 0).
rewrite /Bezout_step; have [g u v a' b' Bezout_a'b' gcd_g H1 H2] := egcdrP.
by rewrite !mxE !addr0 {1}H1 {1}H2 !mulrA -mulrDl Bezout_a'b' mul1r.
Qed.

Lemma sdvd_Bezout_step (m n : nat) (M : 'M_(1 + m,1 + n)) (k : 'I_m) :
 ~~ (M 0 0 %| M (lift 0 k) 0) ->
 (Bezout_step (M 0 0) (M (lift 0 k) 0) M k) 0 0 %<| M 0 0.
Proof.
move=> H; rewrite /sdvdr (eqd_dvd (Bezout_step_mx00 _) (eqdd _)) dvdr_gcdl /=.
rewrite (eqd_dvd (eqdd _ ) (Bezout_step_mx00 _)); apply: contra H => H'.
exact: (dvdr_trans H' (dvdr_gcdr _ _)).
Qed.

Lemma unit_Bezout_mx m a b (k : 'I_m) : Bezout_mx a b k \in unitmx.
Proof.
rewrite /Bezout_mx; case:egcdrP=> g a1 b1 u v Huv Hg Ha1 Hb1.
have H: a1 * u - b1 * -v = 1; first by rewrite mulrN opprK.
by case: (mulmx1_unit (combine_mx_inv k H)).
Qed.

End Bezout_mx.

End BezoutDomainTheory.

(* Section Mixins. *)

(* Variable R : GRing.IntegralDomain.type. *)
(* Variable bezout : R -> R -> (R * ((R * R)) * (R * R)). *)
(* Hypothesis bezout_axiom1 : forall a b, GCDDomain.gcdP a b (bezout a b).1. *)
(* Hypothesis bezout_axiom2 : forall a b, bezoutP a b (bezout a b). *)

(* Definition gcd a b := (bezout a b).1. *)
(* (* ((bezout a b).1,((bezout a b).2.1.1,(bezout a b).2.1.2)). *) *)

(* Lemma bezoutGcdP : forall a b, GCDDomain.gcdP a b (gcd a b). *)
(* Proof. exact: bezout_axiom1. Qed. *)

(* Lemma bezoutGcdMax : forall a b g' x y, GCDDomain.gcdP a b (g',(x,y)) -> *)
(*   exists z, g' * z = (gcd a b).1. *)
(* Proof. *)
(* rewrite /GCDDomain.gcdP /gcd=> a b g' x' y' /= g'P. *)
(* case hbez: (bezout _ _)=> [[g [x y]] [u v]] /=. *)
(* exists (x' * u + y' * v). *)
(* move: (bezout_axiom1 a b) (bezout_axiom2 a b). *)
(* rewrite hbez /GCDDomain.gcdP /bezoutP /= -!g'P => hgxy. *)
(* rewrite mulr_addr !mulrA -!hgxy -!mulrA -mulr_addr. *)
(* by move->; rewrite mulr1. *)
(* Qed. *)

(* Definition GcdMixin := GcdDomainMixin bezoutGcdP bezoutGcdMax. *)

(* End Mixins. *)

Module PID.

Record mixin_of (R : dvdRingType) : Type := Mixin {
  _ : well_founded (@sdvdr R)
}.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : BezoutDomain.class_of R;
  mixin : mixin_of (DvdRing.Pack base)
}.
Local Coercion base : class_of >-> BezoutDomain.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@DvdRing.Pack T b0)) :=
  fun bT b & phant_id (BezoutDomain.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m).

Definition eqType := Equality.Pack class.
Definition choiceType := Choice.Pack class.
Definition zmodType := GRing.Zmodule.Pack class.
Definition ringType := GRing.Ring.Pack class.
Definition comRingType := GRing.ComRing.Pack class.
Definition unitRingType := GRing.UnitRing.Pack class.
Definition comUnitRingType := GRing.ComUnitRing.Pack class.
Definition idomainType := GRing.IntegralDomain.Pack class.
Definition dvdRingType := DvdRing.Pack class.
Definition gcdDomainType := GcdDomain.Pack class.
Definition bezoutDomainType := BezoutDomain.Pack class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> BezoutDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion dvdRingType : type >-> DvdRing.type.
Canonical Structure dvdRingType.
Coercion gcdDomainType : type >-> GcdDomain.type.
Canonical Structure gcdDomainType.
Coercion bezoutDomainType : type >-> BezoutDomain.type.
Canonical Structure bezoutDomainType.
Notation pidType := type.
Notation PIDType T m := (@pack T _ m _ _ id _ id).
Notation PIDMixin := Mixin.
Notation "[ 'pidType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'pidType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pidType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'pidType'  'of'  T ]") : form_scope.
End Exports.
End PID.
Export PID.Exports.

Section PIDTheory.

Variable R : pidType.

Implicit Types a b : R.

Lemma sdvdr_wf : well_founded (@sdvdr R). Proof. by case: R=> [? [? []]]. Qed.
Definition sdvdr_rect := (well_founded_induction_type (sdvdr_wf)).
Definition sdvdr_rec := (well_founded_induction (sdvdr_wf)).
Definition sdvdr_ind := (well_founded_ind (sdvdr_wf)).

End PIDTheory.

Module EuclideanDomain.

Variant edivr_spec (R : ringType)
  (norm : R -> nat) (a b : R) : R * R -> Type :=
  EdivrSpec q r of a = q * b + r & (b != 0) ==> (norm r < norm b)
  : edivr_spec norm a b (q,r).

Record mixin_of (R : ringType) : Type := Mixin {
  enorm : R -> nat;
  ediv : R -> R -> (R * R);
  _ : forall a b, a != 0 -> enorm b <= enorm (a * b);
  (* _ : enorm 0 = 0%N; *)
  _ : forall a b, edivr_spec enorm a b (ediv a b)
}.

Module Dvd.
Section Dvd.
Variable R : idomainType.
Implicit Type a b : R.

Hypothesis mR : mixin_of [ringType of R].
Local Notation norm := (enorm mR).
Local Notation ediv := (ediv mR).

Definition div a b := if b == 0 then 0 else (ediv a b).1.

Local Notation "a %/ b" := (div a b) : ring_scope.
Local Notation "a %% b" := (ediv a b).2 : ring_scope.

Lemma norm_mul : forall a b, a != 0 -> norm b <= norm (a * b).
Proof. by case: mR. Qed.

Lemma edivP : forall a b, edivr_spec norm a b (ediv a b).
Proof. by case: mR. Defined.

Lemma norm0_lt : forall a, a != 0 -> norm 0 < norm a.
Proof.
move=> a a0; case: (edivP a a)=> q r ha; rewrite a0 /= => hr.
apply: leq_trans (hr); rewrite ltnS; apply: contraLR hr.
move/eqP: ha; rewrite addrC -(can2_eq (@addrNK _ _) (@addrK _ _)).
rewrite -{1}[a]mul1r -mulrBl eq_sym -leqNgt.
have [-> | q1] := eqVneq (1 - q) 0; rewrite ?mul0r => /eqP->; rewrite ?leqnn //.
by move=> _; rewrite norm_mul.
Qed.

Definition odiv a b :=
  let (q, r) := ediv a b in
  if r == 0 then Some (if b == 0 then 0 else q) else None.

Lemma odivP a b : DvdRing.div_spec a b (odiv a b).
Proof.
rewrite /odiv; case: edivP=> q r -> hr.
have [-> | r0] := eqVneq r 0; constructor.
  by rewrite addr0; case: ifP => // /eqP->; rewrite !mulr0.
move=> x; case: (eqVneq b 0) hr => /= [-> _|b0 hr].
  by rewrite !mulr0 add0r.
rewrite addrC (can2_eq (@addrK _ _) (@addrNK _ _)) -mulrBl.
have [-> | xq] := eqVneq (x - q) 0; first by rewrite mul0r.
by apply: contraL hr; rewrite -leqNgt => /eqP->; exact: norm_mul.
Qed.

Lemma odiv_def a b : odiv a b = if a %% b == 0 then Some (a %/ b) else None.
Proof. by rewrite /odiv /div; case: ediv. Qed.

Definition Mixin := DvdRingMixin odivP.
End Dvd.
End Dvd.

Module Gcd.
Section Gcd.
Variable R : dvdRingType.
Implicit Type a b : R.

Hypothesis mR : mixin_of [ringType of R].
Local Notation norm := (enorm mR).
Local Notation ediv := (ediv mR).

Definition div a b := if b == 0 then 0 else (ediv a b).1.

Local Notation "a %/ b" := (div a b) : ring_scope.
Local Notation "a %% b" := (ediv a b).2 : ring_scope.
Local Notation edivP := (Dvd.edivP mR).
Local Notation norm_mul := (Dvd.norm_mul mR).
Local Notation norm0_lt := (Dvd.norm0_lt mR).

Lemma leq_norm : forall a b, b != 0 -> a %| b -> norm a <= norm b.
Proof.
move=> a b b0; move/dvdrP => [x hx]; rewrite hx norm_mul //.
by apply: contra b0; rewrite hx; move/eqP->; rewrite mul0r.
Qed.

Lemma ltn_norm : forall a b, b != 0 -> a %<| b -> norm a < norm b.
Proof.
move=> a b b0; case/andP=> ab.
case: (edivP a b)=> q r; rewrite b0 /= => ha nrb; rewrite {1}ha.
have [-> | r0] := eqVneq r 0; first by rewrite addr0 dvdr_mull.
rewrite dvdr_addr ?dvdr_mull // (leq_trans _ nrb) // ltnS leq_norm ?r0 //.
by move: (dvdrr a); rewrite {2}ha dvdr_addr ?dvdr_mull.
Qed.

Lemma sdvdr_wf : well_founded (@sdvdr [dvdRingType of R]).
Proof.
move=> a; wlog: a / a != 0=> [ha|].
  have [-> | a0] := eqVneq a 0; last by apply: ha; rewrite a0.
  constructor=> b; rewrite sdvdr0; apply: ha.
elim: (norm a) {-2}a (leqnn (norm a))=> [|n ihn] {}a ha a0.
  by constructor=> x; move/(ltn_norm a0); rewrite ltnNge (leq_trans ha) ?leq0n.
constructor=> x hx; move/(ltn_norm a0):(hx)=> hn; apply: ihn.
  by rewrite -ltnS (leq_trans hn).
by apply: contra a0 => /eqP x0; move/sdvdrW:hx; rewrite x0 dvd0r.
Qed.

Definition EuclidPID := PIDMixin sdvdr_wf.

Lemma mod_eq0 a b : (a %% b == 0) = (b %| a).
Proof.
case: (edivP a b)=> q r -> /=.
have [-> | /= b0] := eqVneq b 0; first by rewrite mulr0 dvd0r add0r.
move=> nrb; apply/eqP/idP=> [->|].
  by apply/dvdrP; exists q; rewrite addr0.
rewrite dvdr_addr ?dvdr_mull //.
have [-> // | r0] := eqVneq r 0.
by move/leq_norm; rewrite leqNgt r0 nrb => /(_ isT).
Qed.

Lemma norm_eq0 a : norm a = 0%N -> a = 0.
Proof.
apply: contra_eq; rewrite -lt0n => a0.
exact/leq_trans/(norm0_lt a0).
Qed.

Lemma mod_spec: forall a b, b != 0 -> norm (a %% b) < (norm b).
Proof. by move=> a b b0; case: edivP=> q r; rewrite b0. Qed.

Lemma modr0 a : a %% 0 = a.
Proof. by case: edivP=> q r; rewrite mulr0 add0r=> ->. Qed.

Lemma mod0r a : 0 %% a = 0.
Proof.
have [-> | a0] := eqVneq a 0; first by rewrite modr0.
case: edivP=> q r; rewrite a0 /= => /eqP.
rewrite eq_sym (can2_eq (@addKr _ _) (@addNKr _ _)) addr0 => /eqP->.
rewrite -mulNr; apply: contraTeq; rewrite -leqNgt.
by move/leq_norm; apply; exact: dvdr_mull.
Qed.

Lemma dvd_mod a b g : (g %| a) && (g %| b) = (g %| b) && (g %| a %% b).
Proof.
case: edivP=> q r /= -> _.
by case gb: (g %| b); rewrite (andbT, andbF) // dvdr_addr ?dvdr_mull.
Qed.


(* Acc experiment: *)
Lemma tool : forall (a b: R), (b != 0) ==> (norm (a %% b) < norm b).
Proof.
move => a b.
apply/implyP => h.
case: (edivP a b) => q r h1 /=.
by move/implyP; apply.
Qed.

Definition acc_gcd (n:nat) (hn: Acc (fun x y => x < y) n) :
  forall (a b:R), n  = norm b -> R.
elim hn using acc_dep.
move => {}n {}hn hi a b heq.
move: (@tool a b).
case: (b == 0).
- move => _; exact a.
set r := (a %% b).
case: (r == 0).
- move => _; exact b.
move/implyP => h.
apply: (hi (norm r) _ b r (refl_equal (norm r))).
rewrite heq.
by apply: h.
Defined.

Lemma acc_gcdP : forall (n:nat) (hn: Acc (fun x y => x < y) n)
 (a b: R) (hb: n = norm b) (g :R),
 g %| (acc_gcd hn a hb) = (g %| a) && (g %| b).
Proof.
move => n hn.
elim hn using acc_dep.
move => {}n {}hn hi a b heq g /=.
move: (@tool a b).
case b0: (b == 0).
- move => _.
  by rewrite (eqP b0) (dvdr0) andbT.
case r0: ( a %% b == 0).
- move => _.
  by rewrite dvd_mod (eqP r0) dvdr0 andbT.
move => h2.
rewrite (hi (norm (a %% b)) _ b (a %% b) (refl_equal (norm (a %% b))) g).
by rewrite -{1}dvd_mod.
Qed.

Definition GCD (a b:R) : R :=
  acc_gcd (guarded 100 ssr_lt_wf (norm b)) a (refl_equal (norm b)).

Lemma GCDP : forall d a b, d %| GCD a b = (d %| a) && (d %| b).
Proof. by rewrite /GCD => d a b; apply: acc_gcdP. Qed.

Definition gcd a b :=
  let: (a1, b1) := if norm a < norm b then (b, a) else (a, b) in
  if a1 == 0 then b1 else
  let fix loop (n : nat) (aa bb : R) {struct n} :=
      let rr := aa %% bb in
      if rr == 0 then bb else
      if n is n1.+1 then loop n1 bb rr else rr in
  loop (norm a1) a1 b1.

Lemma gcdP : forall d a b, d %| gcd a b = (d %| a) && (d %| b).
Proof.
move=> d a b; rewrite /gcd.
wlog nba: a b / norm b <= norm a=>[hwlog|].
  case: ltnP=> nab.
    by move/hwlog:(ltnW nab); rewrite ltnNge (ltnW nab) /= andbC.
  by move/hwlog:(nab); rewrite ltnNge nab.
rewrite ltnNge nba /=.
have [-> | a0] := eqVneq a 0; first by rewrite dvdr0.
move: (norm a) {-1 3}a nba a0=> n {}a hn a0.
elim: n {-2}n (leqnn n) a b hn a0 => [|k ihk] n hk a b hn a0.
  move: hk hn; rewrite leqn0; move/eqP->; rewrite leqn0.
  by move/eqP/norm_eq0->; rewrite modr0 (negbTE a0) dvdr0 andbT.
move: hk hn; rewrite leq_eqVlt; case/orP; last first.
  by rewrite ltnS=> hnk nb; rewrite ihk.
move/eqP->; rewrite dvd_mod.
case: eqP => [->|_]; first by rewrite dvdr0 andbT.
have [-> | b0] := eqVneq b 0.
  rewrite !modr0 dvdr0 /=.
  by case: k {ihk}=> [|k]; rewrite mod0r eqxx.
by move=> nb; rewrite ihk // -ltnS (leq_trans (mod_spec _ _)).
Qed.

Definition AccMixin := GcdDomainMixin GCDP.
Definition Mixin := GcdDomainMixin gcdP.
End Gcd.
End Gcd.

Module Bezout.
Section Bezout.

Variable R : gcdDomainType.
Implicit Type a b : R.

Hypothesis mR : mixin_of [ringType of R].
Local Notation norm := (enorm mR).
Local Notation ediv := (ediv mR).

Definition div a b := if b == 0 then 0 else (ediv a b).1.

Local Notation "a %/ b" := (div a b) : ring_scope.
Local Notation "a %% b" := (ediv a b).2 : ring_scope.
Local Notation edivP := (Dvd.edivP mR).
Local Notation norm_mul := (Dvd.norm_mul mR).
Local Notation norm0_lt := (Dvd.norm0_lt mR).
Local Notation norm_eq0 := (@Gcd.norm_eq0 _ mR).

Fixpoint egcd_rec (a b : R) n {struct n} : R * R :=
  if n is n'.+1 then
    if b == 0 then (1, 0) else
    let: (u, v) := egcd_rec b (a %% b) n' in
      (v, (u - v * (a %/ b)))
  else (1, 0).

Definition egcd p q := egcd_rec p q (norm q).

Lemma gcdrE : forall a b, gcdr a b %= gcdr b (a %% b).
Proof.
move=> a b; rewrite /eqd dvdr_gcd dvdr_gcdr /=.
case: edivP=> q r /= G _.
move/eqP: (G); rewrite addrC -subr_eq; move/eqP=> H.
rewrite -{1}H dvdr_sub ?dvdr_gcdl //; last by rewrite dvdr_mull ?dvdr_gcdr.
by rewrite dvdr_gcd dvdr_gcdl G dvdr_add ?dvdr_gcdr // dvdr_mull ?dvdr_gcdl.
Qed.

Lemma egcd_recP : forall n a b, norm b <= n
  -> let e := (egcd_rec a b n) in gcdr a b %= e.1 * a + e.2 * b.
Proof.
elim=> [|n ihn] a b /=.
  by rewrite leqn0 => /eqP/norm_eq0->; rewrite mul1r mul0r addr0 gcdr0.
move=> nbSn.
case b0: (b == 0)=> /=; first by rewrite (eqP b0) mul1r mulr0 addr0 gcdr0.
have := (ihn b (a %% b) _).
case: (egcd_rec _ _)=> u v=> /= ihn' /=.
rewrite (eqd_trans (gcdrE _ _)) ?(eqd_trans (ihn' _ _)) //;
  do ?by rewrite -ltnS (leq_trans (mod_spec _ _)) ?b0 //.
rewrite mulrBl addrA [v * a + _]addrC -mulrA -addrA -mulrBr /div b0.
case: edivP ihn'=> /= q r.
move/eqP; rewrite addrC -subr_eq; move/eqP=>->.
by rewrite b0 /= => nrb; apply; rewrite -ltnS (leq_trans nrb).
Qed.

Lemma egcdP : forall a b, BezoutDomain.bezout_spec a b (egcd a b).
Proof.
rewrite /egcd=> a b.
case H: egcd_rec=> [x y]; constructor.
by move: (@egcd_recP _ a b (leqnn _)); rewrite H.
Qed.

Definition Mixin := BezoutDomainMixin egcdP.
End Bezout.
End Bezout.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : PID.class_of R;
  mixin : mixin_of (GRing.Ring.Pack base)
}.
Local Coercion base : class_of >-> PID.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@GRing.Ring.Pack T b0)) :=
  fun bT b & phant_id (PID.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m).

Definition eqType := Equality.Pack class.
Definition choiceType := Choice.Pack class.
Definition zmodType := GRing.Zmodule.Pack class.
Definition ringType := GRing.Ring.Pack class.
Definition comRingType := GRing.ComRing.Pack class.
Definition unitRingType := GRing.UnitRing.Pack class.
Definition comUnitRingType := GRing.ComUnitRing.Pack class.
Definition idomainType := GRing.IntegralDomain.Pack class.
Definition dvdRingType := DvdRing.Pack class.
Definition gcdDomainType := GcdDomain.Pack class.
Definition bezoutDomainType := BezoutDomain.Pack class.
Definition pidType := PID.Pack class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PID.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion dvdRingType : type >-> DvdRing.type.
Canonical Structure dvdRingType.
Coercion gcdDomainType : type >-> GcdDomain.type.
Canonical Structure gcdDomainType.
Coercion bezoutDomainType : type >-> BezoutDomain.type.
Canonical Structure bezoutDomainType.
Coercion pidType : type >-> PID.type.
Canonical Structure pidType.
Notation euclidDomainType := type.
Notation EuclidDomainType T m := (@pack T _ m _ _ id _ id).
Notation EuclidDomainMixin := Mixin.
Notation "[ 'euclidDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'euclidDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'euclidDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'euclidDomainType'  'of'  T ]") : form_scope.
Definition EuclidDvdMixin := @Dvd.Mixin.
Definition EuclidGcdMixin := @Gcd.Mixin.
Definition EuclidGCDMixin := @Gcd.AccMixin.
Definition EuclidPIDMixin := @Gcd.EuclidPID.
Definition EuclidBezoutMixin := @Bezout.Mixin.
End Exports.
End EuclideanDomain.
Export EuclideanDomain.Exports.

Definition edivr (R : euclidDomainType) :=
  EuclideanDomain.ediv (EuclideanDomain.class R).
Definition enorm (R : euclidDomainType) :=
  EuclideanDomain.enorm (EuclideanDomain.class R).


Definition GCD (R : euclidDomainType) :=
    EuclideanDomain.Gcd.GCD (EuclideanDomain.class R).
Definition ACC_GCD (R : euclidDomainType) :=
    @EuclideanDomain.Gcd.acc_gcd _ (EuclideanDomain.class R).

Definition divr (R : euclidDomainType) (m d : R) := (edivr m d).1.
Notation "m %/ d" := (divr m d) : ring_scope.
Definition modr (R : euclidDomainType) (m d : R) := (edivr m d).2.
Notation "m %% d" := (modr m d) : ring_scope.
Notation "m = n %[mod d ]" := (m %% d = n %% d) : ring_scope.
Notation "m == n %[mod d ]" := (m %% d == n %% d) : ring_scope.
Notation "m <> n %[mod d ]" := (m %% d <> n %% d) : ring_scope.
Notation "m != n %[mod d ]" := (m %% d != n %% d) : ring_scope.

Section EuclideanDomainTheory.

Variable R : euclidDomainType.

Implicit Types a b : R.

Lemma enorm_mul : forall a b, a != 0 -> enorm b <= enorm (a * b).
Proof. by case: R=> [? [? []]]. Qed.

(* Lemma enorm0 : enorm (0 : R) = 0%N. Proof. by case: R=> [? [? []]]. Qed. *)

Lemma edivrP : forall a b, EuclideanDomain.edivr_spec (@enorm _) a b (edivr a b).
Proof. by case: R=> [? [? []]]. Qed.

Lemma enorm0_lt : forall a, a != 0 -> enorm (0 : R) < enorm a.
Proof. exact: EuclideanDomain.Dvd.norm0_lt. Qed.

Lemma leq_enorm : forall a b, b != 0 -> a %| b -> enorm a <= enorm b.
Proof. exact: EuclideanDomain.Gcd.leq_norm. Qed.

Lemma ltn_enorm : forall a b, b != 0 -> a %<| b -> enorm a < enorm b.
Proof. exact: EuclideanDomain.Gcd.ltn_norm. Qed.

Lemma modr_eq0 : forall a b, (a %% b == 0) = (b %| a).
Proof. exact: EuclideanDomain.Gcd.mod_eq0. Qed.

Lemma enorm_eq0 : forall a, enorm a = 0%N -> a = 0.
Proof. exact: EuclideanDomain.Gcd.norm_eq0. Qed.

Lemma modr_spec: forall a b, b != 0 -> enorm (a %% b) < (enorm b).
Proof. exact: EuclideanDomain.Gcd.mod_spec. Qed.

Lemma modr0 : forall a, a %% 0 = a.
Proof. exact: EuclideanDomain.Gcd.modr0. Qed.

Lemma mod0r : forall a, 0 %% a = 0.
Proof.
apply: EuclideanDomain.Gcd.mod0r;
exact: (DvdRing.class [dvdRingType of R]).
Qed.

Lemma dvdr_mod : forall a b d, (d %| a) && (d %| b) = (d %| b) && (d %| a %% b).
Proof. exact: EuclideanDomain.Gcd.dvd_mod. Qed.

Lemma divr_mulKr a b : b != 0 -> (b * a) %/ b = a.
Proof.
move=> H.
have: (b * a) %% b = 0.
  by apply/eqP; rewrite modr_eq0 dvdr_mulr // dvdrr.
rewrite /divr /modr.
case: edivrP=> c r He Hb /= Hr.
rewrite Hr addr0 mulrC in He.
by apply: (mulIf H).
Qed.

Lemma divr_mulKl a b : b != 0 -> (a * b) %/ b = a.
Proof.
by rewrite mulrC; apply: divr_mulKr.
Qed.

End EuclideanDomainTheory.
