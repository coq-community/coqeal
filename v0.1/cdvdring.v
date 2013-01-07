(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm tuple choice.
Require Import matrix bigop zmodp mxalgebra poly.
Require Import cssralg dvdring seqmatrix.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

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

Lemma odflt_cdivE d :
  {morph trans : x y / odflt d (x %/? y) >-> odflt (@trans _ CR d) (cdiv x y)}.
Proof. by move=> x y /=; rewrite -cdivE; case: odivrP. Qed.

Definition cdvd x y := @cdiv R CR y x : bool.

Lemma cdvdE x y : x %| y  = cdvd (trans x) (trans y).
Proof. by rewrite /dvdr /cdvd -cdivE; case: odivrP. Qed.

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
     - Add computable gcdsr
     - Add computable lcmsr
*)


(*
Definition cgcds R CR := foldr (@cgcd R CR) (zero CR).
Definition lcmsr R := foldr (@lcmr R) 1.
*)

Section CGcdRingTheory.

Variable R : gcdRingType.
Variable CR : cgcdRingType R.

Lemma cgcdE : {morph (@trans _ CR) : x y / gcdr x y >-> cgcd x y}.
Proof. by case: CR => ? [] ? []. Qed.

Definition clcm (a b : CR) :=
  if (a == zero CR) || (b == zero CR) then zero CR
  else odflt (zero CR) (cdiv (mul a b) (cgcd a b)).

Lemma clcmE : {morph (@trans _ CR) : x y / lcmr x y >-> clcm x y}.
Proof.
rewrite /lcmr /clcm => x y /=; rewrite !trans_eq0.
case: ifP => _; first by rewrite zeroE.
rewrite -mulE -cgcdE -cdivE.
by case: odivrP => //;  rewrite zeroE.
Qed.

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

Let zero := zero CR.
Let one := one CR.

Definition cegcdr (a b : CR) :=
  let: (u, v) := cbezout a b in
    let g := add (mul u a) (mul v b) in
      let a1 := odflt zero (cdiv a g) in
        let b1 := odflt zero (cdiv b g) in
          if g == zero then (zero,one,zero,one,zero) else (g, u, v, a1, b1).

Lemma cegcdrE : forall x y,
  let: (g,u,v,a1,b1) := egcdr x y in
  let: (g',u',v',a1',b1') := cegcdr (trans x) (trans y) in
  [/\ trans g = g', trans u = u', trans v = v', trans a1 = a1' & trans b1 = b1'].
Proof.
move=> x y.
rewrite /egcdr /cegcdr -cbezoutE -!mulE -addE trans_eq0 -!cdivE.
case: (bezout x y)=> a b /=.
case: ifP => _; first by rewrite oneE zeroE.
by split=> //; case: odivrP => //=; rewrite zeroE.
Qed.

Fixpoint cprincipal_gen n (xs : seqmatrix CR) : CR := match n with
  | 0 => zero
  | S p => let x := xs 0%N 0%N in
           let y := cprincipal_gen p (rsubseqmx 1 xs) in
           let: (g,_,_,_,_) := cegcdr x y in g
end.

(* Definition trans_seqrow n (I : 'rV[R]_n) : seqrow CR := *)
(*   [seq trans (I 0 i) | i <- enum 'I_n]. *)

Lemma cprincipal_genE : forall n (I : 'rV[R]_n),
  trans (principal_gen I) = cprincipal_gen n (trans I).
Proof.
elim => /= [_| n ih]; first by rewrite zeroE.
rewrite [n.+1]/(1 + n)%N=> I.
rewrite rsubseqmxE -ih.
have -> : (seqmx_of_mx CR I) 0%N 0%N = trans (I 0 0) by rewrite -seqmxE.
move: (cegcdrE (I 0 0) (principal_gen (rsubmx I))).
case: egcdr=> [[[[g ? ? ? ?]]]].
by case: cegcdr=> [[[[g' ? ? ? ? []]]]].
Qed.

Definition cprincipal n (I : seqmatrix CR) : seqmatrix CR := [:: [:: cprincipal_gen n I]].

Lemma cprincipalE : forall n (I : 'rV[R]_n),
  trans (principal I) = cprincipal n (trans I).
Proof.
move=> n I.
by rewrite /cprincipal /principal /trans /= -scalar_seqmxE cprincipal_genE.
Qed.

(* (x) \subset (x1...xn) iff exists (v1...vn) such that (x1...xn)(v1...vn)^T = (x) *)
Fixpoint cprincipal_w1 n (I : seqmatrix CR) : seqmatrix CR := match n with
  | 0 => [::]
  | S p => let g := cprincipal_gen p (rsubseqmx 1 I) in
           let us := cprincipal_w1 p (rsubseqmx 1 I) in
           let: (g',u,v,a1,b1) := cegcdr (I 0%N 0%N) g in
           [:: u] :: [seq [seq mul v u'' | u'' <- u' ] | u' <- us]
end.

Lemma cprincipal_w1E : forall n (I : 'rV[R]_n),
  trans (principal_w1 I) = cprincipal_w1 n (trans I).
Proof.
elim => /= [_| n ih]; first by rewrite zeroE.
rewrite [n.+1]/(1 + n)%N=> I.
rewrite rsubseqmxE -ih -cprincipal_genE.
have -> : (seqmx_of_mx CR I) 0%N 0%N = trans (I 0 0) by rewrite -seqmxE.
move: (cegcdrE (I 0 0) (principal_gen (rsubmx I))).
case: egcdr=> [[[[g u v ? ?]]]].
case: cegcdr=> [[[[g' u' v' ? ? []]]]] => h1 h2 h3 _ _.
rewrite /trans /= -[seqmx_of_mx _ (col_mx u%:M (v*:principal_w1 _))]col_seqmxE.
by rewrite /col_seqmx -scalar_seqmxE -scaleseqmxE h3 /scaleseqmx h2.
Qed.

(* (x1...xn) \subset (x) iff exists (w1...wn) such that (x)(w1...wn) = (x1...xn) *)
Definition cprincipal_w2 n (I : seqmatrix CR) : seqmatrix CR :=
  let g := cprincipal_gen n I in
  map_seqmx (fun x => odflt zero (cdiv x g)) I.

Lemma cprincipal_w2E : forall n (I : 'rV[R]_n),
  trans (principal_w2 I) = cprincipal_w2 n (trans I).
Proof.
rewrite /principal_w2 /cprincipal_w2 => n I /=.
suff h : {morph trans : x / odflt 0 (x %/? principal_gen I) >->
                        odflt zero (cdiv x (cprincipal_gen n (trans I)))}.
  rewrite -(map_seqmxE _ h); congr trans.
  by apply/matrixP => i j; rewrite !mxE.
by move=> x /=; rewrite odflt_cdivE zeroE cprincipal_genE.
Qed.

End CBezoutRingTheory.

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