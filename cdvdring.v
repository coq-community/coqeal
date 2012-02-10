Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg cssralg.
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
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
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
Coercion choiceType: type >-> Choice.type.
Canonical Structure choiceType.
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
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
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
Coercion choiceType: type >-> Choice.type.
Canonical Structure choiceType.
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

(* Mixins showing that euclidean ring -> bezout and gcd rings *)
Module Mixins.
Section Mixins.

Variable R CR : Type.
Implicit Type phR : phant R.
Implicit Type a b : CR.

Hypothesis cR : EuclideanRing.class_of R.

Canonical Structure R_eqType := EqType R cR.
Canonical Structure R_choiceType := ChoiceType R (Choice.mixin cR).
Canonical Structure R_zmod := @GRing.Zmodule.Pack R cR R.
Canonical Structure R_ring := @GRing.Ring.Pack R cR R.
Canonical Structure R_com :=  @GRing.ComRing.Pack R cR R.
Canonical Structure R_unit := @GRing.UnitRing.Pack R cR R.
Canonical Structure R_comunit := [comUnitRingType of R].
Canonical Structure R_idom := @GRing.IntegralDomain.Pack R cR R.
Canonical Structure R_euclid := @EuclideanRing.Pack R cR R.

Hypothesis cCR : CRing.class_of [ringType of R] CR.

Canonical Structure CR_eqType := EqType CR cCR.
Canonical Structure CR_choiceType := ChoiceType CR (Choice.mixin cCR).
Canonical Structure CR_zmod := @CZmodule.Pack [zmodType of R] (Phant R) CR cCR CR.
Canonical Structure CR_ring := @CRing.Pack [ringType of R] (Phant R) CR cCR CR.

Hypothesis mR : mixin_of [cringType CR of R].

Local Notation cnorm := (cnorm mR).
Local Notation cediv := (cediv mR).

Definition czero := (@zero _ [czmodType R of CR]).

Lemma cnormE : forall x, cnorm (trans x) = enorm x.
Proof. by case: mR. Qed.

Lemma cedivE :
  forall x y, cediv (trans x) (trans y) = (trans (x %/ y),trans (x %% y)).
Proof. by case: mR. Qed.

Definition R_dvdMixin := EuclidDvdMixin R cR.
Canonical Structure R_dvdRingType := DvdRingType R R_dvdMixin.

Definition codiv a b := let (q, r) := cediv a b in
  if r == czero then Some (if b == czero then czero else q) else None.

Lemma odivE : forall x y,
  omap trans (x %/? y) = codiv (trans x) (trans y).
Proof.
rewrite /odivr /= /EuclideanRing.Mixins.odiv /codiv => x y.
rewrite cedivE !trans_eq0 /divr /modr /edivr /=.
case: EuclideanRing.ediv=> a b /=.
do 2! case: ifP => _ //=.
by rewrite zeroE.
Qed.

Lemma codivE : forall x y,
  omap trans (x %/? y) = codiv (trans x) (trans y).
Proof.
move=> x y.
by rewrite odivE.
Qed.

Definition CEuclidDvd := CDvdRingMixin codivE.

(*

Hypothesis dvdM : CDvdRing.mixin_of [cringType CR of R].
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
rewrite mulr_subl addrA [v * a + _]addrC -mulrA -addrA -mulr_subr /div b0.
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

*)

End Mixins.
End Mixins.

(*
Definition CEuclidDvdMixin R CR cR cCR (m0 : mixin_of cCR) :=
  fun bT b  & phant_id (GRing.IntegralDomain.class bT) b =>
  fun     m & phant_id m0 m => @Mixins.CEuclidDvd R b m.
*)
(*
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
*)

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
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
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
Coercion choiceType: type >-> Choice.type.
Canonical Structure choiceType.
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