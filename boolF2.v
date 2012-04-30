Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice.
Require Import fintype bigop finset prime fingroup ssralg finalg.

(* Additive group structure. *)

Lemma bool_add0z : left_id false xorb.
Proof. by case. Qed.

Lemma bool_addNz : left_inverse false id xorb.
Proof. by case. Qed.

Lemma bool_addA : associative xorb.
Proof. by case; case; case. Qed.

Lemma bool_addC : commutative xorb.
Proof. by case; case. Qed.

Definition bool_zmodMixin := ZmodMixin bool_addA bool_addC bool_add0z bool_addNz.
Canonical Structure bool_zmodType := Eval hnf in ZmodType bool bool_zmodMixin.
Canonical Structure bool_finZmodType := Eval hnf in [finZmodType of bool].
Canonical Structure bool_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of bool for +%R].
Canonical Structure bool_finGroupType :=
  Eval hnf in [finGroupType of bool for +%R].

(* Ring operations *)

Lemma bool_mul_addr : right_distributive andb xorb.
Proof. by case; case; case. Qed.

Lemma bool_mul_addl : left_distributive andb xorb.
Proof. by case; case; case. Qed.

Lemma bool_nontrivial : (1 != 0)%bool. Proof. by []. Qed.

Definition bool_ringMixin :=
  ComRingMixin andbA andbC andTb bool_mul_addl
               bool_nontrivial.
Canonical Structure bool_ringType := Eval hnf in RingType bool bool_ringMixin.
Canonical Structure bool_finRingType := Eval hnf in [finRingType of bool].
Canonical Structure bool_comRingType := Eval hnf in ComRingType bool andbC.
Canonical Structure bool_finComRingType := Eval hnf in [finComRingType of bool].

Lemma bool_mulVz : {in pred1 true, left_inverse true id *%R}.
Proof. by move=> b; rewrite !inE; move/eqP=> ->. Qed.

Lemma bool_mulzV x : x == true -> andb x (id x) = true.
Proof. by move/eqP=> ->. Qed.

Lemma bool_boolro_unit : forall x y, andb y x = true -> pred1 true x.
Proof. by case; case. Qed.

Lemma bool_inv_out : {in predC (pred1 true), id =1 id}.
Proof. by []. Qed.

Definition bool_unitRingMixin :=
  @ComUnitRingMixin bool_comRingType (pred1 true) id bool_mulVz bool_boolro_unit bool_inv_out.
Canonical Structure bool_unitRingType :=
  Eval hnf in UnitRingType bool bool_unitRingMixin.
Canonical Structure bool_finUnitRingType := Eval hnf in [finUnitRingType of bool].
Canonical Structure bool_comUnitRingType := Eval hnf in [comUnitRingType of bool].
Canonical Structure bool_finComUnitRingType :=
  Eval hnf in [finComUnitRingType of bool].

Lemma bool_fieldMixin : GRing.Field.mixin_of bool_unitRingType.
Proof. by case. Qed.

Definition bool_idomainMixin := FieldIdomainMixin bool_fieldMixin.

Canonical bool_idomainType := Eval hnf in IdomainType bool  bool_idomainMixin.
Canonical bool_finIdomainType := Eval hnf in [finIdomainType of bool].
Canonical bool_fieldType := Eval hnf in FieldType bool bool_fieldMixin.
Canonical bool_finFieldType := Eval hnf in [finFieldType of bool].
Canonical bool_decFieldType :=
  Eval hnf in [decFieldType of bool for bool_finFieldType].



(* Computable ring structure *)
Require Import cssralg.

Local Open Scope ring_scope.

Implicit Types x y : bool.

Definition bid : bool -> bool := @id bool.

Definition bool_czMixin := id_Mixins.id_czMixin [zmodType of bool].

Canonical Structure bool_czType :=
  Eval hnf in CZmodType bool bool bool_czMixin.

Lemma bool1 : bid true = true.
Proof. by []. Qed.

Lemma qmulP : {morph bid : x y / x * y >-> x * y}.
Proof. by []. Qed.

Definition bool_cringMixin := @CRingMixin [ringType of bool] [czmodType bool of bool]
  1 (fun x y => x * y) bool1 qmulP.

Canonical Structure bool_cringType :=
  Eval hnf in CRingType [ringType of bool] bool_cringMixin.

Lemma unitbool : forall x, pred1 true x = pred1 true (bid x).
Proof. by []. Qed.

Lemma invbool : {morph bid : x / id x >-> id x}.
Proof. by []. Qed.

Definition bool_cunitRingMixin := @CUnitRingMixin [unitRingType of bool] [cringType bool of bool]
  (pred1 true) id unitbool invbool.

Canonical Structure bool_cunitRingType :=
  Eval hnf in CUnitRingType [unitRingType of bool] bool_cunitRingMixin.
