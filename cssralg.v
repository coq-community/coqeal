(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg bigop.

(** This file defines computable structures on top of ssreflect's 
algebraic structures (from ssralg.v) *)

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Record trans_struct (A B: Type) : Type := Trans {
  f : A -> B;
  _ : injective f
}.

Lemma id_inj : forall (A : Type), injective (@id A).
Proof. by move => x y. Qed.

Definition id_trans_struct A := Trans (@id_inj A).

(** Computable Z-modules *)
Module CZmodule.

Record mixin_of (V : zmodType) (T: Type) : Type := Mixin {
  zero : T;
  opp : T -> T;
  add : T -> T -> T;
  tstruct : trans_struct V T;
  _ : (f tstruct) 0 = zero;
  _ : {morph (f tstruct) : x / - x >-> opp x};
  _ : {morph (f tstruct) : x y / x + y >-> add x y}
}.

Section ClassDef.

Variable V : zmodType.

Record class_of T := Class {
  base : Choice.class_of T;
  mixin : mixin_of V T
}.

Local Coercion base : class_of >-> Choice.class_of.

Structure type (phV : phant V) :=
  Pack {sort; _ : class_of sort ; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (phV : phant V) (T : Type) (cT : type phV).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phV T c T.
Definition pack b0 (m0 : mixin_of V (@Choice.Pack T b0 T)) :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m & phant_id m0 m => Pack phV (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Notation czmodType V := (type (Phant V)).
Notation CZmodType V T m := (@pack _ (Phant V) T _ m _ _ id _ id).
Notation CZmodMixin := Mixin.
Notation "[ 'czmodType' V 'of' T 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'czmodType' V 'of' T 'for' cT ]") : form_scope.
Notation "[ 'czmodType' V 'of' T ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'czmodType' V 'of' T ]") : form_scope.
End Exports.

End CZmodule.

Import CZmodule.Exports.

Definition zero (V: zmodType) (T: czmodType V) :=
  CZmodule.zero (CZmodule.class T).
Definition opp (V: zmodType) (T: czmodType V) :=
  CZmodule.opp (CZmodule.class T).
Definition add (V: zmodType) (T: czmodType V) :=
  CZmodule.add (CZmodule.class T).
Definition trans {V: zmodType} {T: czmodType V} :=
  f (CZmodule.tstruct (CZmodule.class T)).

Section CZmoduleTheory.

Variable V : zmodType.
Variable T : czmodType V.

Implicit Types x y : T.

Lemma inj_trans : injective (@trans V T).
Proof. by case: T => ? [] ? [] ? ? ? []. Qed.

Lemma zeroE : @trans V T 0 = (zero _).
Proof. by case: T => ? [] ? [].  Qed.

Lemma addE : {morph (@trans V T) : x y / x + y >-> add x y}.
Proof. by case: T => ? [] ? []. Qed.

Lemma oppE : {morph (@trans V T) : x / - x >-> opp x}.
Proof. by case: T => ? [] ? []. Qed.

Lemma trans_eq0 : forall a, (trans a == zero T) = (a == 0).
Proof.
move=> a.
apply/eqP/eqP=> [h|->].
  by apply/inj_trans; rewrite h zeroE.
by rewrite zeroE.
Qed.

Definition sub x y := add x (opp y).

Lemma subE : {morph (@trans V T) : x y / x - y >-> sub x y }.
Proof.
move=> x y /=.
by rewrite addE oppE.
Qed.

End CZmoduleTheory.

Export CZmodule.Exports.

(** Computable rings *)
Module CRing.

Record mixin_of (R : ringType) (V : czmodType R) : Type := Mixin {
  one : V;
  mul : V -> V -> V;
  _ : trans 1 = one;
  _ : {morph trans : x y / x * y >-> mul x y}
}.

Section ClassDef.

Variable R : ringType.
Implicit Type phR : phant R.

Structure class_of (V : Type) := Class {
  base : CZmodule.class_of R V;
  mixin : mixin_of (CZmodule.Pack _ base V)
}.

Local Coercion base : class_of >-> CZmodule.class_of.

Structure type phR : Type :=
 Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):=
  let: Pack _ c _ := cT return class_of cT in c.

Definition clone phR T cT c of phant_id (@class phR cT) c :=
 @Pack phR T c T.

Definition pack phR T V0 (m0 : mixin_of (@CZmodule.Pack R _ T V0 T)) :=
  fun bT b & phant_id (@CZmodule.class _ phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> CZmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType: type >-> Choice.type.
Canonical Structure choiceType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.

Notation cringType V := (@type _ (Phant V)).
Notation CRingType V m := (@pack _ (Phant V) _ _ m _ _ id _ id).
Notation CRingMixin := Mixin.
Notation "[ 'cringType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'cringType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'cringType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'cringType' T 'of'  V ]") : form_scope.
End Exports.

End CRing.

Import CRing.Exports.

Definition one (R: ringType) (T: cringType R) :=
  CRing.one (CRing.class T).
Definition mul (R: ringType) (T: cringType R) :=
  CRing.mul (CRing.class T).

Section CRingTheory.

Variable R : ringType.
Variable T : cringType R.

Implicit Types x y : T.

Lemma oneE : @trans R T 1 = (one _).
Proof. by case: T => ? [] ? [].  Qed.

Lemma mulE : {morph (@trans R T) : x y / x * y >-> mul x y}.
Proof. by case: T => ? [] ? []. Qed.

End CRingTheory.

Export CRing.Exports.

(** Computable unit rings *)
Module CUnitRing.

Record mixin_of (R : unitRingType) (V : cringType R) : Type := Mixin {
  cunit : pred V;
  cinv  : V -> V;
  _     : forall x, GRing.unit x = cunit (trans x);
  _     : {morph trans : x / GRing.inv x >-> cinv x}
}.

Section ClassDef.

Variable R : unitRingType.
Implicit Type phR : phant R.

Structure class_of (V : Type) := Class {
  base  : CRing.class_of R V;
  mixin : mixin_of (CRing.Pack _ base V)
}.

Local Coercion base : class_of >-> CRing.class_of.

Structure type phR : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):= let: Pack _ c _ := cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.
Definition pack phR T V0 (m0 : mixin_of (@CRing.Pack R _ T V0 T)) :=
  fun bT b & phant_id (@CRing.class _ phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.
Definition cringType phR cT := CRing.Pack phR (@class phR cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType: type >-> Choice.type.
Canonical Structure choiceType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.
Coercion cringType: type >-> CRing.type.
Canonical Structure cringType.

Notation cunitRingType V := (@type _ (Phant V)).
Notation CUnitRingType V m := (@pack _ (Phant V) _ _ m _ _ id _ id).
Notation CUnitRingMixin := Mixin.
Notation "[ 'cunitRingType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'cunitRingType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'cunitRingType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'cunitRingType' T 'of'  V ]") : form_scope.
End Exports.

End CUnitRing.

Import CUnitRing.Exports.

Definition cunit (R: unitRingType) (T: cunitRingType R) :=
  CUnitRing.cunit (CUnitRing.class T).
Definition cinv (R: unitRingType) (T: cunitRingType R) :=
  CUnitRing.cinv (CUnitRing.class T).

Section CUnitRingTheory.

Variable R : unitRingType.
Variable CR : cunitRingType R.

Lemma cunitE : forall x, GRing.unit x = cunit (@trans _ CR x).
Proof. by case: CR => ? [] ? []. Qed.

Lemma cinvE : {morph (@trans _ CR) : x / x^-1 >-> cinv x}.
Proof. by case: CR => ? [] ? []. Qed.

Definition cudiv x y : CR := mul x (cinv y).

Lemma cudivE : {morph trans : x y / x / y >-> cudiv x y}.
Proof.
move=> x y /=.
by rewrite /cudiv mulE cinvE.
Qed.

End CUnitRingTheory.

Export CUnitRing.Exports.

(** Identity mixins *)
Module id_Mixins.
Section id_czMixin.

Variable V : zmodType.

Definition idV := @id V.

Lemma id0 : idV 0 = 0.
Proof. by []. Qed.

Lemma id_opp: {morph idV : x / - x >-> -x}.
Proof. by []. Qed.

Lemma id_add : {morph idV : x y / x + y >-> x + y}.
Proof. by []. Qed.

Definition id_czMixin := @CZmodule.Mixin [zmodType of V] V 0
  (fun x => - x) (fun x y => x + y) (@id_trans_struct V) id0 id_opp id_add.

End id_czMixin.

Section id_cringMixin.

Variable R : ringType.

Definition R_czMixin := id_czMixin [zmodType of R].

Canonical Structure R_czType :=
  Eval hnf in CZmodType R R R_czMixin.

Definition idR := @id R.

Lemma id1 : idR 1 = 1.
Proof. by []. Qed.

Lemma id_mul : {morph idR : x y / x * y >-> x * y}.
Proof. by []. Qed.

Definition id_cringMixin := @CRing.Mixin R [czmodType R of R]
  1 (fun x y => x * y) id1 id_mul.

End id_cringMixin.
End id_Mixins.