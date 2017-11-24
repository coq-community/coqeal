(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm tuple choice.
Require Import matrix bigop zmodp mxalgebra poly. (* generic_quotient. *)

(* Require Import generic_quotient. (* testing *) *)

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* tools for Acc induction *)

Scheme acc_dep := Induction for Acc Sort Type.

(* vsiles: maybe we can reuse lt_wf but I didn't managed to do it *)
Lemma lt_wf2 : well_founded (fun x y => x < y).
Proof.
red in |- *.
have: (forall (n:nat) (a:nat), a < n -> Acc (fun x y => x < y) a).
- elim => [ | n hi] a; first done.
  move => ltaSn. apply: Acc_intro.
  move => b ltba. apply : hi.
  apply : (leq_trans ltba ltaSn).
move => h a.
by apply: (h (a.+1)).
Defined.

Section GUARD.
Variable A: Type.
Variable P : A -> A -> Prop.

Fixpoint guarded (n:nat) (Wf : well_founded P) : well_founded P :=
  match n with
  | O => Wf
  | S n => fun x =>
     (@Acc_intro _ _ x (fun y _ => guarded n (guarded n Wf) y))
end.
End GUARD.


(** Explicit divisibility ring *)
Module DvdRing.

(* Specification of division: div_spec a b == b | a *)
CoInductive div_spec (R : ringType) (a b :R) : option R -> Type :=
| DivDvd x of a = x * b : div_spec a b (Some x)
| DivNDvd of (forall x, a != x * b) : div_spec a b None.

Record mixin_of (R : ringType) : Type := Mixin {
  div : R -> R -> option R;
  _ : forall a b, div_spec a b (div a b)
  }.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : GRing.IntegralDomain.class_of R;
  mixin : mixin_of (GRing.IntegralDomain.Pack base R)
}.
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@GRing.IntegralDomain.Pack T b0 T)) :=
  fun bT b & phant_id (GRing.IntegralDomain.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.

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

Lemma odiv0r : forall a, a != 0 -> 0 %/? a = Some 0.
Proof.
move=> a.
case: odivrP=> [x|H _]; last by by move: (H 0); rewrite mul0r eq_refl.
by move/eqP; rewrite eq_sym mulf_eq0; case/orP; move/eqP->; rewrite // eq_refl.
Qed.

Lemma odivr0 : forall a, a != 0 -> a %/? 0 = None.
Proof.
by move=> a; case: odivrP=> // x; rewrite mulr0=> ->; rewrite eq_refl.
Qed.

Lemma odivr1 : forall a, a %/? 1 = Some a.
Proof.
move=> a.
case: odivrP=> [x|H].
  by rewrite mulr1=> ->.
by move: (H a); rewrite mulr1 eq_refl.
Qed.

Lemma odivrr : forall a, a != 0 -> a %/? a = Some 1.
Proof.
move=> a a0.
case: odivrP=> [x|H].
  by rewrite -{1}[a]mul1r; move/(mulIf a0) <-.
by move: (H 1); rewrite mul1r eq_refl.
Qed.

Lemma odivr_mulrK : forall a b, a != 0 -> b * a %/? a = Some b.
Proof.
move=> a b a0.
case: odivrP=> [x|H].
  by move/(mulIf a0) ->.
by move: (H b); rewrite eq_refl.
Qed.

Lemma odivr_mulKr : forall a b, a != 0 -> a * b %/? a = Some b.
Proof. by move=> a b a0; rewrite mulrC odivr_mulrK. Qed.

Lemma odivr_mul2l : forall a b c, a != 0 -> b != 0 -> a * b %/? (a * c) = (b %/? c).
Proof.
move=> a b c a0 b0.
case c0: (c == 0); first by rewrite (eqP c0) mulr0 !odivr0 // mulf_neq0.
case: odivrP=> [x|H].
  rewrite mulrCA; move/(mulfI a0).
  case: (odivrP b c)=> [x' ->|H]; first by move/(mulIf (negbT c0)) ->.
  by move=> Hbxc; move: (H x); rewrite Hbxc eq_refl.
by case: odivrP=> //x Hbxc; move: (H x); rewrite mulrCA Hbxc eq_refl.
Qed.

Lemma odivr_mul2r : forall a b c, a != 0 -> b != 0 -> b * a %/? (c * a) = (b %/? c).
Proof. by move=> a b c a0 b0; rewrite mulrC [_ * a]mulrC odivr_mul2l. Qed.

Lemma odivr_some : forall a b c, a %/? b = Some c -> a = b * c.
Proof. by move=> a b c; case: odivrP=>// x -> [<-]; rewrite mulrC. Qed.


(** Properties of dvdr *)

Lemma dvdrP : forall a b, reflect (exists x, b = x * a) (a %| b).
Proof.
move=> a b; rewrite /dvdr /=.
case: odivrP=> //= [x|] hx; constructor; first by exists x.
by case=> x; move/eqP; apply: negP (hx _).
Qed.

(****)
Lemma eqdP  (m n :  R) : reflect  (exists2 c12 : R,
     (c12 \is a GRing.unit) & c12 * m = n) 
  (m %= n).
Proof.
apply: (iffP idP). 
  case/andP=> /dvdrP [x Hx] /dvdrP [y Hy].
  case: (altP (@eqP _ n 0))=> Hn. 
    rewrite Hn mulr0 in Hy.
    by exists 1; rewrite ?unitr1 // Hy mulr0 Hn.
  exists x; last by rewrite Hx. 
  apply/GRing.unitrPr; exists y.
  rewrite Hy mulrA in Hx.
  by apply: (mulIf Hn); rewrite -Hx mul1r.
case=> c Hc H; apply/andP; split; apply/dvdrP.
  by exists c; rewrite H.
exists (c^-1); apply: (@mulfI _ c).
  by apply/eqP=> Habs; rewrite Habs unitr0 in Hc.
by rewrite mulrA mulrV // mul1r.
Qed.
(****)

Lemma dvdrr : forall a, a %| a.
Proof. by move=> a; apply/dvdrP; exists 1; rewrite mul1r. Qed.

Hint Resolve dvdrr.

Lemma dvdr_trans : transitive (@dvdr R).
Proof.
move=> b a c; case/dvdrP=> x ->; case/dvdrP=> y ->.
by apply/dvdrP; exists (y * x); rewrite mulrA.
Qed.

Lemma dvdr0 : forall a, a %| 0.
Proof. by move=>a; apply/dvdrP; exists 0; rewrite mul0r. Qed.

Lemma dvd0r : forall a, (0 %| a) = (a == 0) :> bool.
Proof.
move=> a; apply/idP/idP; last by move/eqP->.
by case/dvdrP; move=> x; rewrite mulr0=> ->.
Qed.

Lemma dvdr_add : forall a b c, a %| b -> a %| c -> a %| b + c.
Proof.
move=> a b c; case/dvdrP=>x bax; case/dvdrP=>y cay.
by apply/dvdrP; exists (x + y); rewrite mulrDl bax cay.
Qed.

Lemma dvdrN : forall a b, (a %| (-b)) = (a %| b).
Proof.
move=> a b; apply/dvdrP/dvdrP=> [] [x hx]; exists (-x).
  by rewrite mulNr -hx opprK.
by rewrite hx mulNr.
Qed.

Lemma dvdNr : forall a b, ((-a) %| b) = (a %| b).
Proof.
move=> a b; apply/dvdrP/dvdrP=> [] [x ->]; exists (-x); rewrite ?mulrNN //.
by rewrite mulNr mulrN.
Qed.

Lemma dvdrNN : forall a b, ((-a) %| (-b)) = (a %| b).
Proof. by move=> a b; rewrite dvdNr dvdrN. Qed.

Lemma dvdr_sub : forall a b c, a %| b -> a %| c -> a %| b - c.
Proof. by move=> a b c ab ac; rewrite dvdr_add // dvdrN. Qed.

Lemma dvdr_addl : forall a b c, (b %| a) -> (b %| c + a) = (b %| c).
Proof.
move=> a b c ba; apply/idP/idP=> ha; last exact: dvdr_add.
by rewrite -[c](addrK a) dvdr_sub.
Qed.

Lemma dvdr_addr : forall a b c, (b %| a) -> (b %| a + c) = (b %| c).
Proof. by move=> a b c ba; rewrite addrC dvdr_addl. Qed.

Lemma dvdr_add_eq : forall a b c, (a %| b + c) -> (a %| b) = (a %| c).
Proof. by move=> a b c ha; rewrite -[b](addrK c) dvdr_addr // dvdrN. Qed.

Lemma dvdr_mull : forall c a b, a %| b -> a %| c * b.
Proof.
move=> c a b; move/dvdrP=> [x ->]; apply/dvdrP.
by exists (c * x); rewrite mulrA.
Qed.

Lemma dvdr_mulr : forall b a c, a %| c -> a %| c * b.
Proof. by move=> c a b; rewrite mulrC; apply dvdr_mull. Qed.

Lemma dvdr_mul : forall c d a b, a %| c -> b %| d -> a * b %| c * d.
Proof.
move=> c d a b; case/dvdrP=>x ->; case/dvdrP=> y ->.
by rewrite -mulrCA; apply/dvdrP; exists (y * x); rewrite !mulrA.
Qed.

Lemma dvdr_mul2r : forall c a b, c != 0 -> (a * c %| b * c) = (a %| b) :> bool.
Proof.
move=> c a b c0; apply/idP/idP; last by move/dvdr_mul; apply.
case/dvdrP=> x; move/eqP; rewrite mulrA (inj_eq (mulIf _)) //.
by move/eqP=> hab; apply/dvdrP; exists x.
Qed.

Lemma dvdr_mul2l : forall c a b, c != 0 -> (c * a %| c * b) = (a %| b) :> bool.
Proof. by move=> c a b H; rewrite ![c * _]mulrC dvdr_mul2r. Qed.

Lemma dvd1r : forall a, 1 %| a.
Proof. by move=> a; apply/dvdrP; exists a; rewrite mulr1. Qed.

Hint Resolve dvd1r.


(** Properties of eqd *)

Lemma eqd_def : forall a b, a %= b = (a %| b) && (b %| a).
Proof. by []. Qed.

Lemma eqdd : forall a, a %= a.
Proof. by move=> a; rewrite eqd_def dvdrr. Qed.

Hint Resolve eqdd.

Lemma eqd_sym : symmetric (@eqd R).
Proof. by move=> a b; rewrite eqd_def; apply/andP/andP; case. Qed.

Hint Resolve eqd_sym.

Lemma eqd_trans : transitive (@eqd R).
Proof.
move=> a b c; rewrite !eqd_def; case/andP=> ba ab; case/andP=> ac ca.
by rewrite (dvdr_trans ba) // (dvdr_trans ca).
Qed.

(* Canonical Structure eqd_Equiv := EquivRel eqdd eqd_sym eqd_trans. *)

(* uncomment it when the proof won't get stuck *)

Lemma congr_eqd : forall b d a c, a %= b -> c %= d -> (a %= c) = (b %= d).
Proof.
move=> b d a c ab cd.
apply/idP/idP=> [ac|bd].
  by rewrite eqd_sym in ab; rewrite (eqd_trans (eqd_trans ab ac) cd).
by rewrite eqd_sym in cd; rewrite (eqd_trans ab (eqd_trans bd cd)).
(* Not working: *)
(* by move=> b d a c ab cd; rewrite !equivE (equivP ab) (equivP cd). *)
Qed.

(* Local Notation DR := {R %/ %=R}. *)

Lemma eqdr0 : forall a, (a %= 0) = (a == 0).
Proof. by move=> a; rewrite eqd_def dvdr0 dvd0r. Qed.

Lemma eqd0r : forall a, (0 %= a) = (a == 0).
Proof. by move=> a; rewrite eqd_def dvdr0 dvd0r andbT. Qed.

Lemma eq_eqd : forall a b, a = b -> a %= b.
Proof. by move=> a b <-. Qed.

Lemma eqd_mul : forall c d a b, a %= c -> b %= d -> a * b %= c * d.
Proof. by rewrite /eqd=> c d a b; do 2!case/andP=> ? ?; rewrite !dvdr_mul. Qed.

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

Lemma eqd_mul2l : forall c a b, c != 0 -> (c * a %= c * b) = (a %= b).
Proof. by move=> c a b c0; rewrite eqd_def !dvdr_mul2l. Qed.

Lemma eqd_mul2r : forall c a b, c != 0 -> (a * c %= b * c) = (a %= b).
Proof. by move=> c a b c0; rewrite eqd_def !dvdr_mul2r. Qed.

Lemma eqd_dvd : forall c d a b, a %= c -> b %= d -> (a %| b) = (c %| d).
Proof.
move=> c d a b; rewrite !eqd_def; case/andP=> ca ac; case/andP=> bd db.
apply/idP/idP; first by move/(dvdr_trans ac); move/dvdr_trans; apply.
by move/(dvdr_trans ca); move/dvdr_trans; apply.
Qed.

(****)
Lemma eqd_dvdr (q p d : R) : p %= q -> (d %| p) = (d %| q).  
Proof.
exact: eqd_dvd. 
Qed.

Lemma eqd_dvdl (q p d : R) : p %= q -> (p %| d) = (q %| d).  
Proof.
by move/eqd_dvd; apply. 
Qed.

(* Lemma eqd_ltrans : left_transitive (@eqd R). *)
(* Proof. *)
(* exact: (left_trans eqd_sym eqd_trans). *)
(* Qed. *)

(* Lemma eqd_rtrans : right_transitive (@eqd R). *)
(* Proof. *)
(* exact: (right_trans eqd_sym eqd_trans). *)
(* Qed. *)

Lemma eqd_mulr (q p r : R) : p %= q -> p * r %= q * r.
Proof.
by move/eqd_mul; apply.
Qed.

Lemma eqd_mull (q p r : R) : p %= q -> r * p %= r * q.
Proof.
exact: eqd_mul.
Qed.
(****)


(* dvdr + unit *)

Lemma dvdr1 : forall a, (a %| 1) = (a %= 1).
Proof. by rewrite /eqd=> a; rewrite dvd1r andbT. Qed.

Lemma unitd1 : forall a, (a \in GRing.unit) = (a %= 1).
Proof.
move=> a; rewrite -dvdr1; apply/idP/idP.
  by move=> aH; apply/dvdrP; exists (a^-1); rewrite mulVr.
by case/dvdrP=> x H; apply/unitrP; exists x; rewrite -H mulrC -H.
Qed.

Lemma eqd1 : forall a, a \in GRing.unit -> a %= 1.
Proof. by move=> a; rewrite unitd1. Qed.

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

Lemma dvdUr : forall a b, a %= 1 -> a %| b.
Proof. by move=> a b a1; rewrite (eqd_dvd a1 (eqdd _)) dvd1r. Qed.

Lemma dvdrU : forall b a, b %= 1 -> a %| b = (a %= 1).
Proof. by move=> b a b1; rewrite (eqd_dvd (eqdd _) b1) dvdr1. Qed.

Lemma dvdr_mulr_l: forall b a, b != 0 -> (a * b %| b) = (a %= 1).
Proof. by move=> b a b0; rewrite -{2}[b]mul1r dvdr_mul2r ?dvdr1. Qed.

Lemma dvdr_mull_l : forall b a, b != 0 -> (b * a %| b) = (a %= 1).
Proof.  by move=> b a b0; rewrite mulrC dvdr_mulr_l. Qed.

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

Lemma sdvdrW : forall a b, a %<| b -> a %| b.
Proof. by move=> a b; case/andP. Qed.

Lemma sdvdrNW : forall a b, a %<| b -> ~~(b %| a).
Proof. by move=> a b; case/andP. Qed.

Lemma sdvdr0 : forall a, a %<| 0 = (a != 0).
Proof. by move=> a; rewrite sdvdr_def dvdr0 dvd0r. Qed.

Lemma sdvd0r : forall a, 0 %<| a = false.
Proof. by move=> a; rewrite sdvdr_def dvdr0 andbF. Qed.

(****)
(** bigop **)

Lemma big_dvdr  (I : finType) (d : R) (F : I -> R) (P : pred I) :
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

End DvdRingTheory.

Hint Resolve dvdrr.
Hint Resolve dvd1r.
Hint Resolve eqdd.

(* Notation "x *d y" := (mulqr x y) *)
(*   (at level 40, left associativity, format "x  *d  y"). *)

(* Notation "x %|d y" := (dvdqr x y) *)
(*   (at level 40, left associativity, format "x  %|d  y"). *)


Module GcdRing.

Record mixin_of (R : dvdRingType) : Type := Mixin {
  gcd : R -> R -> R;
  _ : forall a b g, g %| gcd a b = (g %| a) && (g %| b)
}.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : DvdRing.class_of R;
  mixin : mixin_of (DvdRing.Pack base R)
}.
Local Coercion base : class_of >-> DvdRing.class_of.

(* Structure = Record *)
Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@DvdRing.Pack T b0 T)) :=
  fun bT b & phant_id (DvdRing.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition dvdRingType := DvdRing.Pack class cT.

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
Notation gcdRingType := type.
Notation GcdRingType T m := (@pack T _ m _ _ id _ id).
Notation GcdRingMixin := Mixin.
Notation "[ 'gcdRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'gcdRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'gcdRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'gcdRingType'  'of'  T ]") : form_scope.
End Exports.

End GcdRing.
Export GcdRing.Exports.

Definition gcdr R := GcdRing.gcd (GcdRing.class R).

Definition lcmr R a b := nosimpl
  (if (a == 0) || (b == 0) then 0 else odflt 0 ((a * b) %/? (@gcdr R a b))).

Definition gcdsr R := foldr (@gcdr R) 0.
Definition lcmsr R := foldr (@lcmr R) 1.

(* Definition gcdqr (R : gcdRingType) (a b : {R %/ %=R}) : {R %/ %=R} := *)
(*   (\pi (gcdr (repr a) (repr b))). *)


Section GCDRingTheory.

Variable R : gcdRingType.

Implicit Types a b : R.

Lemma dvdr_gcd : forall g a b, g %| gcdr a b = (g %| a) && (g %| b) :> bool.
Proof. by case: R=> [? [? []]]. Qed.

Lemma dvdr_gcdl : forall a b, gcdr a b %| a.
Proof. by move=> a b; move: (dvdrr (gcdr a b)); rewrite dvdr_gcd; case/andP. Qed.

Lemma dvdr_gcdr : forall a b, gcdr a b %| b.
Proof. by move=> a b; move: (dvdrr (gcdr a b)); rewrite dvdr_gcd; case/andP. Qed.

Lemma gcdr_eq0 : forall a b, (gcdr a b == 0) = (a == 0) && (b == 0).
Proof. by move=> a b; rewrite -!dvd0r dvdr_gcd. Qed.

Hint Resolve dvdr_gcdr.
Hint Resolve dvdr_gcdl.

Lemma gcdr_def : forall x a b, x %| a -> x %| b ->
   (forall x', x' %| a -> x' %| b -> (x' %| x)) -> gcdr a b %= x.
Proof. by move=> x a b xa xb hx; rewrite eqd_def dvdr_gcd xa xb hx. Qed.

Lemma gcdrC : forall a b, gcdr a b %= gcdr b a.
Proof. by move=> a b; rewrite /eqd ?dvdr_gcd ?dvdr_gcdr ?dvdr_gcdl. Qed.

Hint Resolve gcdrC.

Lemma eqd_gcd : forall c d a b, a %= c -> b %= d -> gcdr a b %= gcdr c d.
Proof.
move=> c d a b ac bd; rewrite eqd_def !dvdr_gcd.
rewrite -(eqd_dvd (eqdd _) ac) dvdr_gcdl.
rewrite -(eqd_dvd (eqdd _) bd) dvdr_gcdr.
rewrite (eqd_dvd (eqdd _) ac) dvdr_gcdl.
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

Lemma gcd0r : forall a, gcdr 0 a %= a.
Proof. by move=> a; rewrite /eqd dvdr_gcd dvdr0 dvdrr !andbT. Qed.

(* Lemma gcdq0r : forall x : DR, gcdqr (\pi 0) x = x. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcd0r _)). Qed. *)

Lemma gcdr0 : forall a, gcdr a 0 %= a.
Proof. by move=> a; rewrite /eqd dvdr_gcd dvdr0 dvdrr !andbT. Qed.

(* Lemma gcdqr0 : forall x : DR, gcdqr x (\pi 0) = x. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcdr0 _)). Qed. *)

Lemma gcd1r : forall a, gcdr 1 a %= 1.
Proof. by move=> a; rewrite /eqd dvdr_gcd dvdrr dvd1r !andbT. Qed.

(* Lemma gcdq1r : forall x : DR, gcdqr (\pi 1) x = \pi 1. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcd1r _)). Qed. *)

Lemma gcdr1 : forall a, gcdr a 1 %= 1.
Proof. by move=> a; rewrite /eqd dvdr_gcd dvdrr dvd1r !andbT. Qed.

(* Lemma gcdqr1 : forall x : DR, gcdqr x (\pi 1) = \pi 1. *)
(* Proof. by elim/quotW=> x; rewrite gcdqr_pi (equivP (gcdr1 _)). Qed. *)

Lemma gcdrA : forall a b c, gcdr a (gcdr b c) %= gcdr (gcdr a b) c.
Proof.
move=> a b c; rewrite /eqd !dvdr_gcd !dvdr_gcdl !dvdr_gcdr.
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

Lemma gcdrCA : forall a b c, gcdr a (gcdr b c) %= gcdr b (gcdr a c).
Proof.
move=> a b c.
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

Lemma gcdrAC : forall a b c, gcdr (gcdr a b) c %= gcdr (gcdr a c) b.
Proof.
move=> a b c.
rewrite (eqd_trans _ (gcdrA _ _ _)) // eqd_sym (eqd_trans _ (gcdrA _ _ _)) //.
by rewrite (eqd_gcd _ (gcdrC _ _)) //.
Qed.
(*
Proof.
move=> a b c; apply/equivP; rewrite -!(equivP (gcdrA _ _ _)); apply/equivP=> /=.
by rewrite (eqd_gcd (eqdd _) (gcdrC _ _)).
Qed.
*)

Lemma gcdr_mul2r : forall a b c, gcdr (a * c) (b * c) %= gcdr a b * c.
Proof.
move=> a b c.
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

Lemma gcdr_mul2l : forall a b c, gcdr (c * a) (c * b) %= c * gcdr a b.
Proof. by move=> a b c; rewrite ![c * _]mulrC gcdr_mul2r. Qed.

(* Lemma gcdqr_mul2l : forall x y z : DR, gcdqr (z *d x) (z *d y) = z *d gcdqr x y. *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y; elim/quotW=> z. *)
(* by rewrite 2!mulqr_pi 2!gcdqr_pi mulqr_pi (equivP (gcdr_mul2l _ _ _)). *)
(* Qed. *)

Lemma mulr_gcdr : forall a b c, a * gcdr b c %= gcdr (a * b) (a * c).
Proof. by move=> a b c; rewrite eqd_sym gcdr_mul2l. Qed.

Lemma mulr_gcdl : forall a b c, gcdr a b * c %= gcdr (a * c) (b * c).
Proof. by move=> a b c; rewrite eqd_sym gcdr_mul2r. Qed.

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

Lemma gcdr_addr_r : forall c a b, a %| b -> gcdr a (c + b) %= gcdr a c.
Proof.
move=> c a b hab.
rewrite /eqd !dvdr_gcd !dvdr_gcdl dvdr_add ?(dvdr_trans _ hab) //.
by rewrite -{2}[c](@addrK _ b) dvdr_sub // (dvdr_trans _ hab).
Qed.

Lemma gcdr_addl_r : forall c a b, a %| b -> gcdr a (b + c) %= gcdr a c.
Proof. by move=> c a b hab; rewrite addrC gcdr_addr_r. Qed.

Lemma gcdr_addr_l : forall a b c, b %| c -> gcdr (a + c) b %= gcdr a b.
Proof.
move=> a b c Hbc.
by rewrite (eqd_trans (gcdrC _ _)) ?(eqd_trans (gcdr_addr_r _ _)).
Qed.

Lemma gcdr_addl_l : forall a b c, b %| c -> gcdr (c + a) b %= gcdr a b.
Proof.
move=> a b c Hbc.
by rewrite (eqd_trans (gcdrC _ _)) ?(eqd_trans (gcdr_addl_r _ _)).
Qed.

Lemma gcdr_addl_mul : forall a b m, gcdr a (a * m + b) %= gcdr a b.
Proof. by move=> a b m; rewrite gcdr_addl_r // dvdr_mulr. Qed.

(* *)
(* Lemma gcdr_muladdl : forall a b m, gcdr b a %= gcdr (a * m + b) a. *)
(* Admitted. *)
(* *)

(* lcm *)

Lemma dvdr_gcd_mul : forall a b, gcdr a b %| a * b.
Proof. by move=> a b; rewrite dvdr_mull. Qed.

Lemma mulr_lcm_gcd : forall a b, lcmr a b * gcdr a b = a * b.
Proof.
move=> a b; rewrite /lcmr /=; move: (dvdr_gcd_mul a b).
case a0: (a == 0); first by rewrite /= (eqP a0) !mul0r.
case b0: (b == 0); first by rewrite /= (eqP b0) !(mulr0, mul0r).
by rewrite /dvdr; case: odivrP=> // x.
Qed.

Lemma lcmr0 : forall a, lcmr a 0 = 0.
Proof. by move=> a; rewrite /lcmr /= eqxx orbT. Qed.

Lemma lcm0r : forall a, lcmr 0 a = 0.
Proof. by move=> a; rewrite /lcmr eqxx. Qed.

Lemma dvdr_lcm : forall a b c, (lcmr a b %| c) = (a %| c) && (b %| c) :> bool.
Proof.
move=> a b c; case a0: (a == 0).
  rewrite (eqP a0) lcm0r dvd0r.
  by case c0: (c == 0); rewrite // (eqP c0) dvdr0.
case b0: (b == 0).
  rewrite (eqP b0) lcmr0 dvd0r.
  by case c0: (c == 0); rewrite ?andbF // (eqP c0) dvdr0.
rewrite -(@dvdr_mul2r _ (gcdr a b)); last by rewrite gcdr_eq0 a0 b0.
rewrite mulr_lcm_gcd (eqd_dvd (eqdd _) (mulr_gcdr _ _ _)) dvdr_gcd {1}mulrC.
by rewrite !dvdr_mul2r ?a0 ?b0 // andbC.
Qed.

Lemma dvdr_lcml : forall a b, a %| lcmr a b.
Proof.
by move=> a b; move: (dvdrr (lcmr a b)); rewrite dvdr_lcm; case/andP.
Qed.

Hint Resolve dvdr_lcml.

Lemma dvdr_lcmr : forall a b, b %| lcmr a b.
Proof.
by move=> a b; move: (dvdrr (lcmr a b)); rewrite dvdr_lcm; case/andP.
Qed.

Hint Resolve dvdr_lcmr.

Lemma dvdr_gcdr_lcmr : forall a b, gcdr a b %| lcmr a b.
Proof.
move=> a b.
exact: (dvdr_trans (dvdr_gcdl a b) (dvdr_lcml a b)).
Qed.

Lemma lcm1r : forall a, lcmr 1 a %= a.
Proof. by move=> a; rewrite /eqd dvdr_lcm dvdr_lcmr dvdrr dvd1r !andbT. Qed.

Lemma lcmr1 : forall a, lcmr a 1 %= a.
Proof. by move=> a; rewrite /eqd dvdr_lcm dvdr_lcml dvdrr dvd1r !andbT. Qed.

Lemma lcmrC : forall a b, lcmr a b %= lcmr b a.
Proof.
move=> a b; case H0: (gcdr b a == 0).
  by move: H0; rewrite gcdr_eq0; case/andP=> ha; rewrite (eqP ha) lcmr0 lcm0r.
rewrite -(@eqd_mul2r _ (gcdr b a)) ?H0 //.
by rewrite (eqd_trans (eqd_mul (eqdd _) (gcdrC b a))) // !mulr_lcm_gcd mulrC.
Qed.

Lemma lcmrA : forall a b c, lcmr a (lcmr b c) %= lcmr (lcmr a b) c.
Proof.
move=> a b c.
rewrite /eqd !dvdr_lcm !dvdr_lcml !dvdr_lcmr.
rewrite 2!(dvdr_trans _ (dvdr_lcml _ _)) //.
by do 2!rewrite (dvdr_trans _ (dvdr_lcmr _ _)) //.
Qed.

Lemma eqd_lcmr : forall a b c, a %= b -> lcmr a c %= lcmr b c.
Proof.
move=> a b c Hab.
rewrite /eqd !dvdr_lcm !dvdr_lcmr (eqd_dvd Hab (eqdd _)).
by rewrite dvdr_lcml -(eqd_dvd Hab (eqdd _)) dvdr_lcml.
Qed.

Lemma eqd_lcml : forall a b c, a %= b -> lcmr c a %= lcmr c b.
Proof.
move=> a b c Hab.
rewrite (eqd_trans (lcmrC _ _)) // (eqd_trans _ (lcmrC _ _)) //.
by rewrite eqd_lcmr // eqd_sym.
Qed.

Lemma lcmrCA : forall a b c, lcmr a (lcmr b c) %= lcmr b (lcmr a c).
Proof.
move=> a b c.
rewrite (eqd_trans (lcmrA _ _ _)) //.
by rewrite (eqd_trans (eqd_lcmr _ (lcmrC _ _))) // eqd_sym lcmrA.
Qed.

Lemma lcmrAC : forall a b c, lcmr (lcmr a b) c %= lcmr (lcmr a c) b.
Proof.
move=> a b c.
rewrite (eqd_trans _ (lcmrA _ _ _)) //.
by rewrite (eqd_trans _ (eqd_lcml _ (lcmrC _ _))) // eqd_sym lcmrA.
Qed.

Lemma mulr_lcmr : forall a b c, a * lcmr b c %= lcmr (a * b) (a * c).
Proof.
move=> a b c.
case H0: ((a * b == 0) && (a * c == 0)).
  case/andP: H0; rewrite mulf_eq0; case/orP; move/eqP->.
    by rewrite !mul0r lcm0r.
  by rewrite mulr0 !lcm0r mulr0.
rewrite -(@eqd_mul2r _ (gcdr (a * b) (a * c))) ?gcdr_eq0 ?H0 // mulr_lcm_gcd.
rewrite eqd_sym (eqd_trans _ (eqd_mul (eqdd _) (mulr_gcdr a b c))) //.
by rewrite -!mulrA [lcmr b c * _]mulrCA mulr_lcm_gcd [b * _]mulrCA.
Qed.

Lemma mulr_lcml : forall a b c, lcmr a b * c %= lcmr (a * c) (b * c).
Proof. by  move=> a b c; rewrite ![_ * c]mulrC mulr_lcmr. Qed.

Lemma lcmr_mul2r : forall a b c, lcmr (a * c) (b * c) %= lcmr a b * c.
Proof. by move=> a b c; rewrite eqd_sym mulr_lcml. Qed.

Lemma lcmr_mul2l : forall a b c, lcmr (c * a) (c * b) %= c * lcmr a b.
Proof. by move=> a b c; rewrite ![c * _]mulrC lcmr_mul2r. Qed.

Lemma lcmr_mull : forall a b, lcmr a (a * b) %= a * b.
Proof.
move=> a b.
case a0: (a == 0); first by rewrite (eqP a0) mul0r /eqd !lcm0r dvdr0.
rewrite -{1}[a]mulr1 (eqd_trans (lcmr_mul2l 1 b a)) // eqd_mul2l ?a0 //.
exact: (lcm1r b).
Qed.

Lemma lcmr_mulr : forall a b, lcmr b (a * b) %= a * b.
Proof. by move=> a b; rewrite mulrC lcmr_mull. Qed.

Lemma dvdr_lcm_idr : forall a b, a %| b -> lcmr a b %= b.
Proof. by move=> a b; case/dvdrP=>x ->; rewrite lcmr_mulr. Qed.

Lemma dvdr_lcm_idl : forall a b, b %| a -> lcmr a b %= a.
Proof.
by move=> a b; case/dvdrP=> x ->; rewrite (eqd_trans (lcmrC _ _)) // lcmr_mulr.
Qed.

Lemma gcdsr0 : (@gcdsr R) [::] = 0.
Proof. by []. Qed.

Lemma gcdsr_cons : forall a s, gcdsr (a :: s) = gcdr a (gcdsr s).
Proof. by []. Qed.

Lemma dvdr_gcds : forall (l : seq R) (g : R), g %| gcdsr l = all (%|%R g) l.
Proof. by elim=> [|a l ihl] g; rewrite /= ?dvdr0 // dvdr_gcd ihl. Qed.

Lemma dvdr_mem_gcds : forall (l : seq R) (x : R), x \in l -> gcdsr l %| x.
Proof.
by move=> l x hx; move: (dvdrr (gcdsr l)); rewrite dvdr_gcds; move/allP; apply.
Qed.

Lemma lcmsr0 : (@lcmsr R) [::] = 1.
Proof. by []. Qed.

Lemma lcmsr_cons : forall a s, lcmsr (a :: s) = lcmr a (lcmsr s).
Proof. by []. Qed.

Lemma dvdr_lcms : forall (l : seq R) (m : R), lcmsr l %| m = all (%|%R^~ m) l.
Proof. by elim=> [|a l ihl] m; rewrite /= ?dvd1r // dvdr_lcm ihl. Qed.

Lemma dvdr_mem_lcms : forall (l : seq R) (x : R), x \in l -> x %| lcmsr l.
Proof.
by move=> l x hx; move: (dvdrr (lcmsr l)); rewrite dvdr_lcms; move/allP; apply.
Qed.

(* uncomment it when congr_eqd will be fixed *)

(* Coprimality *)
Definition coprimer a b := gcdr a b %= 1.

Lemma coprimer_sym : forall a b, coprimer a b = coprimer b a.
Proof. by move=> a b; rewrite /coprimer; apply: congr_eqd. Qed.

Lemma euclid_inv : forall a b c, coprimer a b -> (a * b %| c) = (a %| c) && (b %| c).
Proof.
move=> a b c cab.
by rewrite -mulr_lcm_gcd (eqd_dvd (eqd_mul (eqdd _) cab) (eqdd _)) mulr1 dvdr_lcm.
Qed.

Lemma euclid : forall b a c, coprimer a b -> (a %| c * b) = (a %| c) :> bool.
Proof.
move=> b a c cab; symmetry.
rewrite -{1}[c]mulr1 -(eqd_dvd (eqdd _) (eqd_mul (eqdd c) cab)).
by rewrite (eqd_dvd (eqdd _) (mulr_gcdr _ _ _)) dvdr_gcd dvdr_mull.
Qed.

Lemma euclid_gcdr : forall a b c, coprimer a b -> gcdr a (c * b) %= gcdr a c.
Proof.
move=> a b c cab.
rewrite eqd_def !dvdr_gcd !dvdr_gcdl /= andbC dvdr_mulr //= -(@euclid b) //.
rewrite /coprimer (eqd_trans (gcdrAC _ _ _)) //.
by rewrite (eqd_trans (eqd_gcd cab (eqdd _))) ?gcd1r.
Qed.

Lemma euclid_gcdl : forall a b c, coprimer a b -> gcdr a (b * c) %= gcdr a c.
Proof. by move=> a b c cab; rewrite mulrC euclid_gcdr. Qed.

Lemma coprimer_mulr : forall a b c, coprimer a (b * c) = coprimer a b && coprimer a c.
Proof.
move=> a b c.
case co_pm: (coprimer a b) => /=.
  by rewrite /coprimer; apply: congr_eqd; rewrite // euclid_gcdl.
apply: negbTE; move/negP: co_pm; move/negP; apply: contra=> cabc.
apply: gcdr_def; rewrite ?dvd1r // => x xa xb.
by rewrite -(eqd_dvd (eqdd _) cabc) dvdr_gcd xa dvdr_mulr.
Qed.

Lemma coprimer_mull : forall a b c, coprimer (b * c) a = coprimer b a && coprimer c a.
Proof. by move=> a b c; rewrite !(coprimer_sym _ a) coprimer_mulr. Qed.

(* *)
(* Lemma coprimerw : forall a b, coprimer a b -> coprimer (gcdrwl a b) (gcdrwr a b). *)
(* Proof. *)
(* move=> a b. *)
(* rewrite /coprimer -eqdU1=> gU. *)
(* case: (@gcdPlr a b)=> aw bw. *)
(* apply eq_eqd in aw; rewrite eqd_sym in aw. *)
(* apply eq_eqd in bw; rewrite eqd_sym in bw. *)
(* apply: (@eqd_gcdrl a _ _ 1); first exact: (eqd_mulUl aw gU). *)
(* apply: (@eqd_gcdrr b _ _ 1); first exact: (eqd_mulUl bw gU). *)
(* by rewrite -eqdU1. *)
(* Qed. *)
(* *)

(** Irreducible and prime elements *)

Definition primer a := ((a == 0 = false)
                   * (a %= 1 = false)
                   * (forall b c, a %| (b * c) = (a %| b) || (a %| c) :> bool)%R)%type.

Definition irredr a := ((a == 0 = false)
                         * (a %= 1 = false)
                         * (forall b c, a %= b * c
                         -> (b %= 1) || (c %= 1))%R)%type.

Lemma irredrP : forall a, irredr a ->
  forall b c, a %= b * c -> b %= 1 \/ c %= 1.
Proof. by move=> ? [ha ia] *; apply/orP; rewrite ia. Qed.

Lemma irredr_dvd : forall a b, irredr a ->  a %| b = ~~(coprimer a b) :> bool.
Proof.
rewrite /coprimer=> a b ia; case g1: (_ %= 1)=> /=.
   apply/negP=> hab; suff: a %= 1 by rewrite ia.
   by rewrite -dvdr1 (@dvdr_trans _ (gcdr a b)) ?dvdr_gcd ?dvdrr // dvdr1.
case: (dvdrP _ _ (dvdr_gcdl a b))=> x hx; rewrite hx.
move/eq_eqd: hx; case/irredrP=> //; last by rewrite g1.
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
case b0: (b == 0); first by rewrite (eqP b0) mul0r eqdr0 ia.
case c0: (c == 0); first by rewrite (eqP c0) mulr0 eqdr0 ia.
rewrite eqd_def ia andb_orl.
case/orP; case/andP; move/(dvdr_trans _)=> h; move/h.
  by rewrite dvdr_mull_l ?b0 // => ->; rewrite orbT.
by rewrite dvdr_mulr_l ?c0 // => ->.
Qed.

(****)
(** bigop **)


Lemma big_dvdr_gcdr (I : finType) (F : I -> R) :
   forall i, \big[(@gcdr R)/0]_i F i %| F i.
Proof.
move=> i; elim: (index_enum I) (mem_index_enum i)=> // a l IHl.
rewrite in_cons big_cons; case/orP=> [/eqP ->|H].
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

End GCDRingTheory.

Module BezoutRing.

CoInductive bezout_spec (R : gcdRingType) (a b : R) : R * R -> Type:=
  BezoutSpec x y of gcdr a b %= x * a + y * b : bezout_spec a b (x, y).

Record mixin_of (R : gcdRingType) : Type := Mixin {
  bezout : R -> R -> (R * R);
   _ : forall a b, bezout_spec a b (bezout a b)
}.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : GcdRing.class_of R;
  mixin : mixin_of (GcdRing.Pack base R)
}.
Local Coercion base : class_of >-> GcdRing.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@GcdRing.Pack T b0 T)) :=
  fun bT b & phant_id (GcdRing.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition dvdRingType := DvdRing.Pack class cT.
Definition gcdRingType := GcdRing.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GcdRing.class_of.
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
Coercion gcdRingType : type >-> GcdRing.type.
Canonical Structure gcdRingType.
Notation bezoutRingType := type.
Notation BezoutRingType T m := (@pack T _ m _ _ id _ id).
Notation BezoutRingMixin := Mixin.
Notation "[ 'bezoutRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'bezoutRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'bezoutRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'bezoutRingType'  'of'  T ]") : form_scope.
End Exports.

End BezoutRing.
Export BezoutRing.Exports.

Definition bezout R := BezoutRing.bezout (BezoutRing.class R).

Section BezoutRingTheory.

Variable R : bezoutRingType.

Implicit Types a b : R.

(* Lemma bezout_gcdPlr : forall a b, GCDRing.gcdP a b (bezout a b).1. *)
(* Proof. by case: R => [? [? []]]. Qed. *)

Lemma bezoutP : forall a b, BezoutRing.bezout_spec a b (bezout a b).
Proof. by case: R=> [? [? []]]. Qed.


Definition egcdr a b :=
  let: (u, v) := bezout a b in
    let g := u * a + v * b in
      let a1 := odflt 0 (a %/? g) in
        let b1 := odflt 0 (b %/? g) in
          if g == 0 then (0,1,0,1,0) else (g, u, v, a1, b1).

CoInductive egcdr_spec a b : R * R * R * R * R -> Type :=
  EgcdrSpec g u v a1 b1 of u * a1 + v * b1 = 1
  & g %= gcdr a b
  & a = a1 * g & b = b1 * g : egcdr_spec a b (g, u, v, a1, b1).

Lemma egcdrP : forall a b, egcdr_spec a b (egcdr a b).
Proof.
move=> a b; rewrite /egcdr; case: bezoutP=> x y hg /=.
move: (dvdr_gcdr a b) (dvdr_gcdl a b); rewrite !(eqd_dvd hg (eqdd _))=> ha hb.
have [g_eq0|g_neq0] := boolP (_ == 0).
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
- by move : hb; rewrite /dvdr; case: odivrP.
by  move: ha; rewrite /dvdr; case: odivrP.
Qed.


(* Proof that any finitely generated ideal is principal *)
(* This could use gcdsr if it would be expressed using bigops... *)
Fixpoint principal_gen n : 'rV[R]_n -> R := match n with
  | 0 => fun _ => 0
  | S p => fun (I : 'rV[R]_(1 + p)) =>
           let x := I 0 0 in
           let y := principal_gen (rsubmx I) in
           let: (g,_,_,_,_) := egcdr x y in g
end.

(* Fixpoint principal_gen n (r : 'rV[R]_n) : R := \big[(fun x y => (egcdr x y).1.1.1.1) /0]_(i < n) (r 0 i). *)


Lemma principal_gen_dvd : forall n (I : 'rV[R]_n) i, principal_gen I %| I 0 i.
Proof.
elim => [I i| n ih]; first by rewrite thinmx0 /= !mxE dvdrr.
rewrite [n.+1]/(1 + n)%nat => I i.
rewrite -[I]hsubmxK !mxE.
case: splitP => j hj /=.
  rewrite !ord1 !mxE /=.
  case: splitP => // j' _.
  rewrite ord1 mxE lshift0.
  case: egcdrP => g u v a b _.
  rewrite eqd_def; case/andP => h _ _ _.
  exact: (dvdr_trans h (dvdr_gcdl _ _)).
case: egcdrP => g u v a b _.
rewrite eqd_def row_mxKr; case/andP => h _ _ _.
apply/(dvdr_trans (dvdr_trans h (dvdr_gcdr _ _))).
by rewrite ih.
Qed.

Definition principal n (I : 'rV[R]_n) : 'M[R]_1 := (principal_gen I)%:M.

(* (x) \subset (x1...xn) iff exists (v1...vn) such that (x1...xn)(v1...vn)^T = (x) *)
Fixpoint principal_w1 n : 'rV[R]_n -> 'cV[R]_n := match n with
  | 0 => fun _ => 0
  | S p => fun (I : 'rV[R]_(1 + p)) =>
           let g := principal_gen (rsubmx I) in
           let us := principal_w1 (rsubmx I) in
           let: (g',u,v,a1,b1) := egcdr (I 0 0) g in
           col_mx u%:M (v *: us)
end.

Lemma principal_w1_correct : forall n (I : 'rV[R]_n),
  I *m principal_w1 I = principal I.
Proof.
elim => [I | n ih]; first by rewrite thinmx0 mulmx0 /principal rmorph0.
rewrite [n.+1]/(1 + n)%nat => I.
rewrite -[I]hsubmxK /principal /= row_mxKr {-1}hsubmxK.
case: egcdrP => g u v a1 b1 hbezout _ h1 h2 /=.
rewrite [row_mx (lsubmx I) _ *m _]mul_row_col -scalemxAr ih /principal h2.
have -> : lsubmx I = (I 0 0)%:M.
  apply/matrixP => i j.
   by rewrite !mxE !ord1 eqxx /= mulr1n lshift0.
rewrite h1 -scalar_mxM mulrC mulrA !scalar_mxM -mul_scalar_mx mulmxA.
by rewrite -mulmxDl -!scalar_mxM -rmorphD hbezout mul1mx.
Qed.

(* (x1...xn) \subset (x) iff exists (w1...wn) such that (x)(w1...wn) = (x1...xn) *)
Definition principal_w2 n (I : 'rV[R]_n) : 'rV[R]_n :=
  let g := principal_gen I in
  map_mx (fun x => odflt 0 (x %/? g)) I.

Lemma principal_w2_correct : forall n (I : 'rV[R]_n),
  principal I *m principal_w2 I = I.
Proof.
move=> n I.
rewrite mul_scalar_mx.
apply/matrixP => i j; rewrite !mxE !ord1 /= {i}.
case: n I j => [I j | n I j]; first by rewrite !thinmx0 /= mul0r !mxE.
case: odivrP => [ x -> | H]; first by rewrite mulrC.
case/dvdrP: (principal_gen_dvd I j)=> x Hx.
move: (H x).
by rewrite Hx eqxx.
Qed.


End BezoutRingTheory.

(* Section Mixins. *)

(* Variable R : GRing.IntegralDomain.type. *)
(* Variable bezout : R -> R -> (R * ((R * R)) * (R * R)). *)
(* Hypothesis bezout_axiom1 : forall a b, GCDRing.gcdP a b (bezout a b).1. *)
(* Hypothesis bezout_axiom2 : forall a b, bezoutP a b (bezout a b). *)

(* Definition gcd a b := (bezout a b).1. *)
(* (* ((bezout a b).1,((bezout a b).2.1.1,(bezout a b).2.1.2)). *) *)

(* Lemma bezoutGcdP : forall a b, GCDRing.gcdP a b (gcd a b). *)
(* Proof. exact: bezout_axiom1. Qed. *)

(* Lemma bezoutGcdMax : forall a b g' x y, GCDRing.gcdP a b (g',(x,y)) -> *)
(*   exists z, g' * z = (gcd a b).1. *)
(* Proof. *)
(* rewrite /GCDRing.gcdP /gcd=> a b g' x' y' /= g'P. *)
(* case hbez: (bezout _ _)=> [[g [x y]] [u v]] /=. *)
(* exists (x' * u + y' * v). *)
(* move: (bezout_axiom1 a b) (bezout_axiom2 a b). *)
(* rewrite hbez /GCDRing.gcdP /bezoutP /= -!g'P => hgxy. *)
(* rewrite mulr_addr !mulrA -!hgxy -!mulrA -mulr_addr. *)
(* by move->; rewrite mulr1. *)
(* Qed. *)

(* Definition GcdMixin := GcdRingMixin bezoutGcdP bezoutGcdMax. *)

(* End Mixins. *)

Module PrincipalRing.


Record mixin_of (R : dvdRingType) : Type := Mixin {
  _ : well_founded (@sdvdr R)
}.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : BezoutRing.class_of R;
  mixin : mixin_of (DvdRing.Pack base R)
}.
Local Coercion base : class_of >-> BezoutRing.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@DvdRing.Pack T b0 T)) :=
  fun bT b & phant_id (BezoutRing.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition dvdRingType := DvdRing.Pack class cT.
Definition gcdRingType := GcdRing.Pack class cT.
Definition bezoutRingType := BezoutRing.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> BezoutRing.class_of.
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
Coercion gcdRingType : type >-> GcdRing.type.
Canonical Structure gcdRingType.
Coercion bezoutRingType : type >-> BezoutRing.type.
Canonical Structure bezoutRingType.
Notation priRingType := type.
Notation PriRingType T m := (@pack T _ m _ _ id _ id).
Notation PriRingMixin := Mixin.
Notation "[ 'priRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'priRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'priRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'priRingType'  'of'  T ]") : form_scope.
End Exports.
End PrincipalRing.
Export PrincipalRing.Exports.

Section PrincipalRingTheory.

Variable R : priRingType.

Implicit Types a b : R.

Lemma sdvdr_wf : well_founded (@sdvdr R). Proof. by case: R=> [? [? []]]. Qed.
Definition sdvdr_rect := (well_founded_induction_type (sdvdr_wf)).
Definition sdvdr_rec := (well_founded_induction (sdvdr_wf)).
Definition sdvdr_ind := (well_founded_ind (sdvdr_wf)).

End PrincipalRingTheory.

Module EuclideanRing.

CoInductive edivr_spec (R : ringType)
  (g : R -> nat) (a b : R) : R * R -> Type :=
  EdivrSpec q r of a = q * b + r & (b != 0) ==> (g r < g b)
  : edivr_spec g a b (q, r).

Record mixin_of (R : ringType) : Type := Mixin {
  enorm : R -> nat;
  ediv : R -> R -> (R * R);
  _ : forall a b, a != 0 -> enorm b <= enorm (a * b);
  (* _ : enorm 0 = 0%N; *)
  _ : forall a b, edivr_spec enorm a b (ediv a b)
}.

Module Mixins.

Section Mixins.

Variable R : Type.
Implicit Type a b : R.

Hypothesis cR : GRing.IntegralDomain.class_of R.

Canonical Structure R_eqType := EqType R cR.
Canonical Structure R_choiceType := ChoiceType R (Choice.mixin cR).
Canonical Structure R_zmod := @GRing.Zmodule.Pack R cR R.
Canonical Structure R_ring := @GRing.Ring.Pack R cR R.
Canonical Structure R_com :=  @GRing.ComRing.Pack R cR R.
Canonical Structure R_unit := @GRing.UnitRing.Pack R cR R.
Canonical Structure R_comunit := [comUnitRingType of R].
Canonical Structure R_idom := @GRing.IntegralDomain.Pack R cR R.

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
case q1: (1 - q == 0); rewrite ?(eqP q1) ?mul0r; move/eqP->; rewrite ?leqnn //.
by move=> _; rewrite norm_mul // q1.
Qed.

Definition odiv a b := let (q, r) := ediv a b in
  if r == 0 then Some (if b == 0 then 0 else q) else None.

Lemma odivP : forall a b, DvdRing.div_spec a b (odiv a b).
Proof.
move=> a b; rewrite /odiv; case: edivP=> q r -> hr.
case r0: (r == 0)=> //=; constructor.
  by rewrite (eqP r0) addr0; case: ifP=> //; move/eqP->; rewrite !mulr0.
move=> x; case b0: (b == 0) hr=> /= hr.
  by rewrite (eqP b0) !mulr0 add0r r0.
rewrite addrC (can2_eq (@addrK _ _) (@addrNK _ _)) -mulrBl.
case xq : (x - q == 0); first by rewrite (eqP xq) mul0r r0.
by apply: contraL hr; rewrite -leqNgt; move/eqP->; rewrite norm_mul ?xq.
Qed.

Lemma odiv_def : forall a b, odiv a b =
  if a %% b == 0 then Some (a %/ b) else None.
Proof. by move=> a b; rewrite /odiv /div; case: ediv. Qed.

Definition EuclidDvd := DvdRingMixin odivP.

Hypothesis dvdM : DvdRing.mixin_of [ringType of R].
Canonical Structure euclidDvdRing := DvdRingType R dvdM.

Lemma leq_norm : forall a b, b != 0 -> a %| b -> norm a <= norm b.
Proof.
move=> a b b0; move/dvdrP=> [x hx]; rewrite hx norm_mul //.
by apply: contra b0; rewrite hx; move/eqP->; rewrite mul0r.
Qed.

Lemma ltn_norm : forall a b, b != 0 -> a %<| b -> norm a < norm b.
Proof.
move=> a b b0; case/andP=> ab.
case: (edivP a b)=> q r; rewrite b0 /= => ha nrb; rewrite {1}ha.
case r0: (r == 0); first by rewrite (eqP r0) addr0  dvdr_mull.
rewrite dvdr_addr ?dvdr_mull // (leq_trans _ nrb) // ltnS leq_norm ?r0 //.
by move: (dvdrr a); rewrite {2}ha dvdr_addr ?dvdr_mull.
Qed.

Lemma sdvdr_wf : well_founded (@sdvdr [dvdRingType of R]).
Proof.
move=> a; wlog: a / a != 0=> [ha|].
  case a0: (a == 0); last by apply: ha; rewrite a0.
  rewrite (eqP a0); constructor=> b; rewrite sdvdr0; apply: ha.
elim: (norm a) {-2}a (leqnn (norm a))=> [|n ihn] {a} a ha a0.
  by constructor=> x; move/(ltn_norm a0); rewrite ltnNge (leq_trans ha) ?leq0n.
constructor=> x hx; move/(ltn_norm a0):(hx)=> hn; apply ihn.
  by rewrite -ltnS (leq_trans hn).
by apply: contra a0; move/eqP=> x0; move/sdvdrW:hx; rewrite x0 dvd0r.
Qed.

Definition EuclidPrincipal := PriRingMixin sdvdr_wf.

Lemma mod_eq0 : forall a b, (a %% b == 0) = (b %| a).
Proof.
move=> a b; case: (edivP a b)=> q r -> /=.
case b0: (b == 0)=> /=; first by rewrite (eqP b0) mulr0 dvd0r add0r.
move=> nrb; apply/eqP/idP=> [->| ].
  by apply/dvdrP; exists q; rewrite addr0.
rewrite dvdr_addr ?dvdr_mull //.
case r0: (r == 0); first by rewrite (eqP r0).
by move/leq_norm; rewrite r0 leqNgt nrb; move/(_ isT).
Qed.

Lemma norm_eq0 : forall a, norm a = 0%N -> a = 0.
Proof.
move=> a; move/eqP=> na0; apply/eqP.
apply: contraLR na0; rewrite -lt0n=> a0.
by rewrite (leq_trans _ (norm0_lt a0)) // ltnS.
Qed.

Lemma mod_spec: forall a b, b != 0 -> norm (a %% b) < (norm b).
Proof. by move=> a b b0; case: edivP=> q r; rewrite b0. Qed.

Lemma modr0 : forall a, a %% 0 = a.
Proof. by move=> a; case: edivP=> q r; rewrite mulr0 add0r=> ->. Qed.

Lemma mod0r : forall a, 0 %% a = 0.
Proof.
move=> a; case a0: (a == 0); first by rewrite (eqP a0) modr0.
case: edivP=> q r; rewrite a0 /=; move/eqP.
rewrite eq_sym (can2_eq (@addKr _ _) (@addNKr _ _)) addr0; move/eqP->.
rewrite -mulNr=> nra; apply/eqP; apply: contraLR nra; rewrite -leqNgt.
by move/leq_norm=> -> //; rewrite dvdr_mull.
Qed.

Lemma dvd_mod : forall a b g, (g %| a) && (g %| b) = (g %| b) && (g %| a %% b).
Proof.
move=> a b g; case: edivP=> q r /= -> _.
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
elim hn using acc_dep. clear n hn.
move => n hn hi a b heq.
move : (@tool a b).
case :(b == 0).
- move => _; exact a.
set r := (a %% b).
case : (r == 0).
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
elim hn using acc_dep. clear n hn.
move => n hn hi a b heq g /=.
move: (@tool a b).
case b0 : (b == 0).
- move => _.
  by rewrite (eqP b0) (dvdr0) andbT.
case r0 : ( a %% b == 0).
- move => _.
  by rewrite dvd_mod (eqP r0) dvdr0 andbT.
move => h2.
rewrite (hi (norm (a %% b)) _ b (a %% b) (refl_equal (norm (a %% b))) g).
by rewrite -{1}dvd_mod.
Qed.

Definition GCD (a b:R) : R :=
  acc_gcd (guarded 100 lt_wf2 (norm b)) a (refl_equal (norm b)).

Lemma GCDP : forall (a b g:R),
  g %| GCD a b = (g %| a) && (g %| b).
Proof.
rewrite /GCD => a b g.
by apply: acc_gcdP.
Qed.

Definition gcd a b :=
  let: (a1, b1) := if norm a < norm b then (b, a) else (a, b) in
  if a1 == 0 then b1 else
  let fix loop (n : nat) (aa bb : R) {struct n} :=
      let rr := aa %% bb in
      if rr == 0 then bb else
      if n is n1.+1 then loop n1 bb rr else rr in
  loop (norm a1) a1 b1.

Lemma gcdP : forall a b g, g %| gcd a b = (g %| a) && (g %| b).
Proof.
move=>  a b g. rewrite /gcd.
wlog nba: a b / norm b <= norm a=>[hwlog|].
  case: ltnP=> nab.
    by move/hwlog:(ltnW nab); rewrite ltnNge (ltnW nab) /= andbC.
  by move/hwlog:(nab); rewrite ltnNge nab.
rewrite ltnNge nba /=.
case a0 : (a == 0).
  by rewrite (eqP a0) dvdr0.
move: (norm a) {-1 3}a nba a0=> n {a} a hn a0.
elim: n {-2}n (leqnn n) a b hn a0=> [|k ihk] n hk a b hn a0.
  move: hk hn; rewrite leqn0; move/eqP->; rewrite leqn0.
  by move/eqP; move/norm_eq0->; rewrite modr0 a0 dvdr0 andbT.
move: hk hn; rewrite leq_eqVlt; case/orP; last first.
  by rewrite ltnS=> hnk nb; rewrite ihk.
move/eqP->; rewrite dvd_mod.
case r0: (_ == _); first by rewrite (eqP r0) dvdr0 andbT.
case b0: (b == 0).
  rewrite (eqP b0) /= !modr0 dvdr0 /=.
  by case: k {ihk}=> [|k]; rewrite mod0r eqxx.
by move=> nb; rewrite ihk // -ltnS (leq_trans (mod_spec _ _)) ?b0.
Qed.

Definition EuclidGCD := GcdRingMixin GCDP.
Definition EuclidGcd := GcdRingMixin gcdP.

Hypothesis gcdM : GcdRing.mixin_of [dvdRingType of R].
Canonical Structure R_gcdRing := GcdRingType R gcdM.

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
  rewrite leqn0.
  (* move/(norm_eq0 (eqP _)). (* <- note : why doesn't it work *) *)
  by move/eqP; move/norm_eq0=>->; rewrite mul1r mul0r addr0 gcdr0.
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

Lemma egcdP : forall a b, BezoutRing.bezout_spec a b (egcd a b).
Proof.
rewrite /egcd=> a b.
case H: egcd_rec=> [x y]; constructor.
by move: (@egcd_recP _ a b (leqnn _)); rewrite H.
Qed.

Definition EuclidBezout := BezoutRingMixin egcdP.

End Mixins.

End Mixins.


Definition EuclidDvdMixin R cR (m0 : mixin_of cR) :=
  fun bT b  & phant_id (GRing.IntegralDomain.class bT) b =>
  fun     m & phant_id m0 m => @Mixins.EuclidDvd R b m.

Definition EuclidGcdMixin R cR (m0 : mixin_of cR) :=
  fun biT bi  & phant_id (GRing.IntegralDomain.class biT) bi =>
  fun bdT bd  & phant_id (DvdRing.class bdT : DvdRing.mixin_of _) bd =>
  fun     m & phant_id m0 m => @Mixins.EuclidGcd R bi m bd.


Definition EuclidGCDMixin R cR (m0 : mixin_of cR) :=
  fun biT bi  & phant_id (GRing.IntegralDomain.class biT) bi =>
  fun bdT bd  & phant_id (DvdRing.class bdT : DvdRing.mixin_of _) bd =>
  fun     m & phant_id m0 m => @Mixins.EuclidGCD R bi m bd.


Definition EuclidBezoutMixin R cR (m0 : mixin_of cR) :=
  fun biT bi  & phant_id (GRing.IntegralDomain.class biT) bi =>
  fun bdT bd  & phant_id (DvdRing.class bdT : DvdRing.mixin_of _) bd =>
  fun bgT bg  & phant_id (GcdRing.class bgT : GcdRing.mixin_of _) bg =>
  fun     m & phant_id m0 m => @Mixins.EuclidBezout R bi m bd bg.

Definition EuclidPriMixin R cR (m0 : mixin_of cR) :=
  fun biT bi  & phant_id (GRing.IntegralDomain.class biT) bi =>
  fun bdT bd  & phant_id (DvdRing.class bdT : DvdRing.mixin_of _) bd =>
  fun     m & phant_id m0 m => @Mixins.EuclidPrincipal R bi m bd.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : PrincipalRing.class_of R;
  mixin : mixin_of (GRing.Ring.Pack base R)
}.
Local Coercion base : class_of >-> PrincipalRing.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@GRing.Ring.Pack T b0 T)) :=
  fun bT b & phant_id (PrincipalRing.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition dvdRingType := DvdRing.Pack class cT.
Definition gcdRingType := GcdRing.Pack class cT.
Definition bezoutRingType := BezoutRing.Pack class cT.
Definition priRingType := PrincipalRing.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PrincipalRing.class_of.
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
Coercion gcdRingType : type >-> GcdRing.type.
Canonical Structure gcdRingType.
Coercion bezoutRingType : type >-> BezoutRing.type.
Canonical Structure bezoutRingType.
Coercion priRingType : type >-> PrincipalRing.type.
Canonical Structure priRingType.
Notation euclidRingType := type.
Notation EuclidRingType T m := (@pack T _ m _ _ id _ id).
Notation EuclidRingMixin := Mixin.
Notation "[ 'euclidRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'euclidRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'euclidRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'euclidRingType'  'of'  T ]") : form_scope.
Notation EuclidDvdMixin T m := (@EuclidDvdMixin T _ m _ _ id _ id).
Notation EuclidGcdMixin T m := (@EuclidGcdMixin T _ m _ _ id _ _ id _ id).
Notation EuclidGCDMixin T m := (@EuclidGCDMixin T _ m _ _ id _ _ id _ id).
Notation EuclidBezoutMixin T m :=
  (@EuclidBezoutMixin T _ m _ _ id _ _ id _ _ id _ id).
Notation EuclidPriMixin T m := (@EuclidPriMixin T _ m _ _ id _ _ id _ id).
End Exports.
End EuclideanRing.
Export EuclideanRing.Exports.

Definition edivr (R : euclidRingType) :=
  EuclideanRing.ediv (EuclideanRing.class R).
Definition enorm (R : euclidRingType) :=
  EuclideanRing.enorm (EuclideanRing.class R).


Definition GCD (R : euclidRingType) :=
    EuclideanRing.Mixins.GCD (EuclideanRing.class R).
Definition ACC_GCD (R : euclidRingType) :=
    @EuclideanRing.Mixins.acc_gcd _ (EuclideanRing.class R).


Definition divr (R : euclidRingType) (m d : R) := (edivr m d).1.
Notation "m %/ d" := (divr m d) : ring_scope.
Definition modr (R : euclidRingType) (m d : R) := (edivr m d).2.
Notation "m %% d" := (modr m d) : ring_scope.
Notation "m = n %[mod d ]" := (m %% d = n %% d) : ring_scope.
Notation "m == n %[mod d ]" := (m %% d == n %% d) : ring_scope.
Notation "m <> n %[mod d ]" := (m %% d <> n %% d) : ring_scope.
Notation "m != n %[mod d ]" := (m %% d != n %% d) : ring_scope.

Section EuclideanRingTheory.

Variable R : euclidRingType.

Implicit Types a b : R.

Lemma enorm_mul : forall a b, a != 0 -> enorm b <= enorm (a * b).
Proof. by case: R=> [? [? []]]. Qed.

(* Lemma enorm0 : enorm (0 : R) = 0%N. Proof. by case: R=> [? [? []]]. Qed. *)

Lemma edivrP : forall a b, EuclideanRing.edivr_spec (@enorm _) a b (edivr a b).
Proof. by case: R=> [? [? []]]. Qed.

Lemma enorm0_lt : forall a, a != 0 -> enorm (0 : R) < enorm a.
Proof. exact: EuclideanRing.Mixins.norm0_lt. Qed.

Lemma leq_enorm : forall a b, b != 0 -> a %| b -> enorm a <= enorm b.
Proof. exact: EuclideanRing.Mixins.leq_norm. Qed.

Lemma ltn_enorm : forall a b, b != 0 -> a %<| b -> enorm a < enorm b.
Proof. exact: EuclideanRing.Mixins.ltn_norm. Qed.

Lemma modr_eq0 : forall a b, (a %% b == 0) = (b %| a).
Proof. exact: EuclideanRing.Mixins.mod_eq0. Qed.

Lemma enorm_eq0 : forall a, enorm a = 0%N -> a = 0.
Proof. exact: EuclideanRing.Mixins.norm_eq0. Qed.

Lemma modr_spec: forall a b, b != 0 -> enorm (a %% b) < (enorm b).
Proof. exact: EuclideanRing.Mixins.mod_spec. Qed.

Lemma modr0 : forall a, a %% 0 = a.
Proof. exact: EuclideanRing.Mixins.modr0. Qed.

Lemma mod0r : forall a, 0 %% a = 0.
Proof.
apply: EuclideanRing.Mixins.mod0r;
exact: (DvdRing.class [dvdRingType of R]).
Qed.

Lemma dvdr_mod : forall a b g, (g %| a) && (g %| b) = (g %| b) && (g %| a %% b).
Proof. exact: EuclideanRing.Mixins.dvd_mod. Qed.

(****)
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
(****)

End EuclideanRingTheory.
