(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path fintype tuple finset ssralg cssralg.
Require Import dvdring.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* Computable explicit divisibility ring *)
Module CDvdRing.

Section ClassDef.

Variable R : dvdRingType.
Implicit Type phR : phant R.

Record mixin_of (CR : cringType R) : Type := Mixin {
  cdiv : CR -> CR -> option CR;
  _ : forall x y, omap trans (x %/? y) = cdiv (trans x) (trans y)
}.

Structure class_of (V : Type) := Class {
  base : CRing.class_of R V;
  mixin : mixin_of (CRing.Pack _ base V)
}.

Local Coercion base : class_of >-> CRing.class_of.

Structure type phR : Type :=
 Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):= let: Pack _ c _ :=
 cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c :=
 @Pack phR T c T.
Definition pack phR T V0 (m0 : mixin_of (@CRing.Pack R _ T V0 T)) :=
  fun bT b & phant_id (@CRing.class _ phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.
Definition cringType phR cT := CRing.Pack phR (@class phR cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.
Coercion cringType: type >-> CRing.type.
Canonical Structure cringType.

Notation cdvdRingType V := (@type _ (Phant V)).
Notation CDvdRingType V m := (@pack _ (Phant V) _ _ m _ _ id _ id).
Notation CDvdRingMixin := Mixin.
Notation "[ 'cdvdRingType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'cdvdRingType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'cdvdRingType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'cdvdRingType' T 'of'  V ]") : form_scope.
End Exports.

End CDvdRing.

Export CDvdRing.Exports.

Definition cdiv (R: dvdRingType) (T: cdvdRingType R) :=
  CDvdRing.cdiv (CDvdRing.class T).

Section CDvdRingTheory.

Variable R : dvdRingType.
Variable CR : cdvdRingType R.

Lemma cdivE : forall x y,
  omap trans (x %/? y) = cdiv (@trans _ CR x) (trans y).
Proof. by case: CR => ? [] ? []. Qed.

End CDvdRingTheory.


(* Computable gcd rings *)
Module CGcdRing.

Section ClassDef.

Variable R : gcdRingType.
Implicit Type phR : phant R.

Record mixin_of (CR : cdvdRingType R) : Type := Mixin {
  cgcd : CR -> CR -> CR;
  _ : {morph trans : x y / gcdr x y >-> cgcd x y}
}.

Record class_of (V : Type) : Type := Class {
  base  : CDvdRing.class_of R V;
  mixin : mixin_of (CDvdRing.Pack _ base V)
}.

Local Coercion base : class_of >-> CDvdRing.class_of.

Structure type phR : Type :=
  Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):= let: Pack _ c _ := cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.
Definition pack phR T V0 (m0 : mixin_of (@CDvdRing.Pack R _ T V0 T)) :=
  fun bT b & phant_id (@CDvdRing.class _ phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.
Definition cringType phR cT := CRing.Pack phR (@class phR cT) cT.
Definition cdvdRingType phR cT := CDvdRing.Pack phR (@class phR cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CDvdRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.
Coercion cringType: type >-> CRing.type.
Canonical Structure cringType.
Coercion cdvdRingType: type >-> CDvdRing.type.
Canonical Structure cdvdRingType.

Notation cgcdRingType V := (@type _ (Phant V)).
Notation CGcdRingType V m := (@pack _ (Phant V) _ _ m _ _ id _ id).
Notation CGcdRingMixin := Mixin.
Notation "[ 'cgcdRingType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'cgcdRingType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'cgcdRingType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'cgcdRingType' T 'of'  V ]") : form_scope.
End Exports.

End CGcdRing.

Export CGcdRing.Exports.

Definition cgcd (R: gcdRingType) (T: cgcdRingType R) :=
  CGcdRing.cgcd (CGcdRing.class T).

(* TODO:
     - Add computable lcm
     - Add computable gcdsr ??
     - Add computable lcmsr ??
*)
(*
Definition clcm R a b := nosimpl
  if (a == 0) || (b == 0) then 0 else odflt 0 ((a * b) %/? (@gcdr R a b)).
Definition cgcds R CR := foldr (@cgcd R CR) (zero CR).
Definition lcmsr R := foldr (@lcmr R) 1.
*)

Section CGcdRingTheory.

Variable R : gcdRingType.
Variable CR : cgcdRingType R.

Lemma cgcdE : {morph (@trans _ CR) : x y / gcdr x y >-> cgcd x y}.
Proof. by case: CR => ? [] ? []. Qed.

(* TODO: Add theory about cgcds? *)

End CGcdRingTheory.


(* Computable Bezout rings *)
Module CBezoutRing.

Section ClassDef.

Variable R : bezoutRingType.
Implicit Type phR : phant R.

Record mixin_of (CR : cgcdRingType R) : Type := Mixin {
  cbezout : CR -> CR -> CR * CR;
  _ : forall x y, (trans (bezout x y).1,trans (bezout x y).2) =
                  cbezout (trans x) (trans y)
}.

Record class_of (V : Type) : Type := Class {
  base  : CGcdRing.class_of R V;
  mixin : mixin_of (CGcdRing.Pack _ base V)
}.

Local Coercion base : class_of >-> CGcdRing.class_of.

Structure type phR : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):= let: Pack _ c _ := cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.
Definition pack phR T V0 (m0 : mixin_of (@CGcdRing.Pack R _ T V0 T)) :=
  fun bT b & phant_id (@CGcdRing.class _ phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.
Definition cringType phR cT := CRing.Pack phR (@class phR cT) cT.
Definition cdvdRingType phR cT := CDvdRing.Pack phR (@class phR cT) cT.
Definition cgcdRingType phR cT := CGcdRing.Pack phR (@class phR cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CGcdRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.
Coercion cringType: type >-> CRing.type.
Canonical Structure cringType.
Coercion cdvdRingType: type >-> CDvdRing.type.
Canonical Structure cdvdRingType.
Coercion cgcdRingType: type >-> CGcdRing.type.
Canonical Structure cgcdRingType.

Notation cbezoutRingType V := (@type _ (Phant V)).
Notation CBezoutRingType V m := (@pack _ (Phant V) _ _ m _ _ id _ id).
Notation CBezoutRingMixin := Mixin.
Notation "[ 'cbezoutRingType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'cbezoutRingType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'cbezoutRingType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'cbezoutRingType' T 'of'  V ]") : form_scope.
End Exports.

End CBezoutRing.

Export CBezoutRing.Exports.

Definition cbezout (R : bezoutRingType) (T : cbezoutRingType R) :=
  CBezoutRing.cbezout (CBezoutRing.class T).

Section CBezoutRingTheory.

Variable R : bezoutRingType.
Variable CR : cbezoutRingType R.

Lemma cbezoutE : forall x y, (@trans _ CR (bezout x y).1,trans (bezout x y).2) =
                             cbezout (trans x) (trans y).
Proof. by case: CR => ? [] ? []. Qed.

End CBezoutRingTheory.

(*
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
  by rewrite mulr_addl mul1r -!mulrA -Ha -Hb.
- by rewrite eqd_sym.
- by move : hb; rewrite /dvdr; case: odivrP.
by  move: ha; rewrite /dvdr; case: odivrP.
Qed.

End BezoutRingTheory.
*)


Module CEuclideanRing.

Record mixin_of (R : euclidRingType) (CR : cringType R) : Type := Mixin {
  cnorm : CR -> nat;
  cediv : CR -> CR -> (CR * CR);
  _ : forall x, cnorm (trans x) = enorm x;
  _ : forall x y, cediv (trans x) (trans y) = (trans (x %/ y),trans (x %% y))
}.


Section ClassDef.

Variable R : euclidRingType.
Implicit Type phR : phant R.

Record class_of (V : Type) : Type := Class {
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
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.
Definition cringType phR cT := CRing.Pack phR (@class phR cT) cT.
(*
Definition cdvdRingType phR cT := CDvdRing.Pack phR (@class phR cT) cT.
Definition cgcdRingType phR cT := CGcdRing.Pack phR (@class phR cT) cT.
Definition cbezoutRingType phR cT := CBezoutRing.Pack phR (@class phR cT) cT.
*)
End ClassDef.

Module Exports.
Coercion base : class_of >-> CRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.
Coercion cringType: type >-> CRing.type.
Canonical Structure cringType.
(*
Coercion cdvdRingType: type >-> CDvdRing.type.
Canonical Structure cdvdRingType.
Coercion cgcdRingType: type >-> CGcdRing.type.
Canonical Structure cgcdRingType.
Coercion cbezoutRingType: type >-> CBezoutRing.type.
Canonical Structure cbezoutRingType.
*)

Notation ceuclidRingType V := (@type _ (Phant V)).
Notation CEuclidRingType V m := (@pack _ (Phant V) _ _ m _ _ id _ id).
Notation CEuclidRingMixin := Mixin.
Notation "[ 'ceuclidRingType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'ceuclidRingType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'ceuclidRingType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'ceuclidRingType' T 'of'  V ]") : form_scope.
End Exports.

End CEuclideanRing.

Export CEuclideanRing.Exports.

Definition cnorm (R : euclidRingType) (T : ceuclidRingType R) :=
  CEuclideanRing.cnorm (CEuclideanRing.class T).

Definition cediv (R : euclidRingType) (T : ceuclidRingType R) :=
  CEuclideanRing.cediv (CEuclideanRing.class T).

Section CEuclideanRingTheory.

Variable R : euclidRingType.
Variable CR : ceuclidRingType R.

Lemma cnormE : forall x, enorm x = cnorm (@trans _ CR x).
Proof. by case: CR => ? [] ? []. Qed.

Lemma cedivE : forall x y, (@trans _ CR (x %/ y),trans (x %% y)) =
                           cediv (trans x) (trans y).
Proof. by case: CR => ? [] ? []. Qed.

End CEuclideanRingTheory.