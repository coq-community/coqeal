(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
From mathcomp Require Import ssralg fintype perm choice matrix bigop zmodp mxalgebra poly.

Require Import ssrcomplements dvdring stronglydiscrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Delimit Scope mxpresentation_scope with MP.
Local Open Scope mxpresentation_scope.

(** Coherent rings *)
Module CoherentRing.

Record mixin_of (R : ringType) : Type := Mixin {
  dim_ker : forall m n, 'M[R]_(m,n) -> nat;
  ker : forall m n (M : 'M_(m,n)), 'M_(dim_ker M,m);
  _ : forall m n (M : 'M_(m,n)) (X : 'rV_m),
      reflect (exists Y, X = Y *m ker M) (X *m M == 0)
}.

Section ClassDef.

(** Coherent rings are based on strongly discrete rings *)
Record class_of (R : Type) : Type := Class {
  base  : StronglyDiscrete.class_of R;
  mixin : mixin_of (StronglyDiscrete.Pack base R)
}.
Local Coercion base : class_of >-> StronglyDiscrete.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@StronglyDiscrete.Pack T b0 T)) :=
  fun bT b & phant_id (StronglyDiscrete.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition unitRingType := GRing.UnitRing.Pack class cT.
Definition comUnitRingType := GRing.ComUnitRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition stronglyDiscreteType := StronglyDiscrete.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> StronglyDiscrete.class_of.
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
Coercion stronglyDiscreteType : type >-> StronglyDiscrete.type.
Canonical Structure stronglyDiscreteType.

Notation coherentRingType := type.
Notation CoherentRingType T m := (@pack T _ m _ _ id _ id).
Notation CoherentRingMixin := Mixin.
Notation "[ 'coherentRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'coherentRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'coherentRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'coherentRingType'  'of'  T ]") : form_scope.
End Exports.

End CoherentRing.
Export CoherentRing.Exports.

Definition dim_ker R := CoherentRing.dim_ker (CoherentRing.class R).
Definition ker R (m n : nat) (M : 'M_(m, n)) :'M_(dim_ker M, m) :=
  @CoherentRing.ker _ (CoherentRing.class R) m n M.

Section CoherentRingTheory.

Variable R : coherentRingType.

Lemma kerP_subproof : forall m n (M : 'M[R]_(m,n)) (X : 'rV_m),
  reflect (exists Y : 'rV_(dim_ker M), X = Y *m ker M) (X *m M == 0).
Proof. by case: R => [? [? []]]. Qed.

Lemma kerK m n (M : 'M[R]_(m,n)) : ker M *m M = 0.
Proof.
rewrite -row_matrixP => i; rewrite row_mul row0.
by apply/eqP/kerP_subproof; exists (delta_mx 0 i); rewrite rowE.
Qed.

Lemma kerAK p m n (M : 'M_(m,n)) (N : 'M[R]_(p, _)) : N *m ker M *m M = 0.
Proof. by rewrite -mulmxA kerK mulmx0. Qed.

Lemma ker1 m : ker (1%:M : 'M[R]_m) = 0.
Proof. by rewrite -kerK mulmx1. Qed.

Lemma kerP m n k (M : 'M[R]_(m,n)) (X : 'M_(k, m)) :
  reflect (exists Y : 'M_(k, dim_ker M), X = Y *m ker M) (X *m M == 0).
Proof.
apply: (iffP idP); last first.
  case=> [Y ->]; apply/eqP; apply/row_matrixP => i.
  by rewrite !row_mul row0 kerAK.
move=> /eqP XM0; have XM0_ i : row i X *m M == 0 by rewrite -row_mul XM0 row0.
exists (\matrix_(i, j) (projT1 (sig_eqW (kerP_subproof _ _ (XM0_ i)))) 0 j).
by apply/row_matrixP => i; rewrite row_mul rowK; case: sig_eqW.
Qed.

(** As everything is based on strongly discrete rings we can solve q systems
    of the kind XM = B *)
Fixpoint divmx m n l : 'M_(l, n) -> 'M[R]_(m, n) -> 'M_(l, m) :=
  match n return 'M_(l, n) -> 'M_(m, n) -> 'M_(l, m) with
   | p.+1 => fun (B: 'M_(_, 1 + _)) (M : 'M_(_, 1 + _)) =>
    let K := ker (lsubmx M) in let W := divid (lsubmx B) (lsubmx M) in
    divmx (rsubmx B - W *m rsubmx M) (K *m rsubmx M) *m K + W
   | _ => fun _ _ => 0
  end.
Definition dvdmx m n k (M : 'M[R]_(m,n)) (N : 'M_(k, n)) :=
  (divmx N M *m M == N).

Local Notation "M %| B" := (dvdmx M B) : mxpresentation_scope.

Lemma dvdmxP m n l (M : 'M[R]_(m, n)) (B : 'M_(l, n)) :
  reflect (exists X, B = X *m M) (M %| B).
Proof.
apply: (iffP eqP)=> [<-|[X -> {B}]]; first by eexists.
elim: n => //= [|n ihn] in m l M X *; first by apply/matrixP => i [].
rewrite -[n.+1]/(1 + n)%N in M X *.
set Ml := lsubmx M; set K := ker _; set W := divid _ _; set k := dim_ker _.
rewrite mulmxDl -mulmxA -!mulmx_rsub -!mulmxBl; apply: canLR (@addrNK _ _) _.
set Mr := rsubmx M; rewrite -mulmxBl -[M]hsubmxK -/Mr -/Ml !mul_mx_row.
have /kerP [Y ->] : (X - W) *m Ml == 0.
  by rewrite mulmxBl dividK -mulmx_lsub ?subrr ?subidMl.
by rewrite -!mulmxA !kerK !mulmx0 ihn.
Qed.

Lemma divmxK m n l (M : 'M[R]_(m, n)) (B : 'M_(l, n)) :
  M %| B -> divmx B M *m M = B.
Proof. by move/eqP. Qed.

Lemma sub_kermxP p m n (A : 'M_(m, n)) (B : 'M_(p, m)) :
  reflect (B *m A = 0) (ker A %| B).
Proof.
apply: (iffP (dvdmxP _ _)); last by move=> /eqP /kerP [X ->]; eexists.
by case=> D ->; rewrite -mulmxA kerK mulmx0.
Qed.

Lemma dvdmx_refl m n (M : 'M[R]_(m,n)) : M %| M .
Proof. by apply/dvdmxP; exists 1%:M; rewrite mul1mx. Qed.
Hint Resolve dvdmx_refl.

Lemma dvdmxMl m0 m1 m2 m3 (M : 'M[R]_(m1,m2)) (N : 'M[R]_(m3,m2))
  (K : 'M[R]_(m0,m3)) : M %| N -> M %| K *m N.
Proof.
by case/dvdmxP=> X hX; apply/dvdmxP; exists (K *m X); rewrite -mulmxA hX.
Qed.

Lemma dvdmx_trans m0 m1 m2 m3
  (M : 'M[R]_(m0,m1)) (N : 'M[R]_(m2,m1)) (K : 'M_(m3,m1)) :
  M %| N -> N %| K -> M %| K.
Proof. by move=> /dvdmxP [X ->] /dvdmxP [Y ->]; rewrite mulmxA dvdmxMl. Qed.

Lemma dvdmx0 k m n (M : 'M[R]_(m,n)) : M %| (0 : 'M[R]_(k,n)).
Proof. by apply/dvdmxP; exists 0; rewrite mul0mx. Qed.
Hint Resolve dvdmx0.

Lemma dvd1mx m n (M : 'M[R]_(m,n)) : 1%:M %| M.
Proof. by apply/dvdmxP; exists M; rewrite mulmx1. Qed.
Hint Resolve dvd1mx.

Lemma dvd0mx k m n (M : 'M[R]_(m,n)) :
  ((0 : 'M[R]_(k,n)) %| M) = (M == 0).
Proof. by apply/idP/eqP => [/dvdmxP [X ->]|-> //]; rewrite mulmx0. Qed.

Lemma dvdmxMr (m0 m1 m2 m3 : nat) (K : 'M_(m2, m0))
     (M : 'M[R]_(m1, m2)) (N : 'M_(m3, m2)) :
   (M %| N) -> (M *m K %| N *m K).
Proof.
by move=> /dvdmxP [X hX]; apply/dvdmxP; exists X; rewrite mulmxA hX.
Qed.

Lemma dvdmxD m0 m1 m2 (M : 'M[R]_(m0,m1)) (N K : 'M[R]_(m2,m1)) :
  M %| N -> M %| K -> M %| N + K.
Proof. by move=> /dvdmxP [X ->] /dvdmxP [Y ->]; rewrite -mulmxDl dvdmxMl. Qed.

Lemma dvdmxN m0 m1 m2 (M : 'M[R]_(m0,m1)) (N : 'M[R]_(m2,m1)) :
  (M %| - N) = (M %| N).
Proof.
by apply/dvdmxP/dvdmxP=> [] [X hX]; exists (- X); rewrite mulNmx -hX ?opprK.
Qed.

Lemma dvdmxDr (m0 m1 m2 : nat)  (N K : 'M_(m2, m1)) (M : 'M[R]_(m0, m1)) :
  M %| N -> (M %| N + K) = (M %| K) :> bool.
Proof.
move=> dvdMN; apply/idP/idP; last exact: (dvdmxD dvdMN).
by rewrite -dvdmxN in dvdMN => /(dvdmxD dvdMN); rewrite addKr.
Qed.

Lemma dvdmxDl (m0 m1 m2 : nat) (N K : 'M_(m2, m1)) (M : 'M[R]_(m0, m1)) :
  M %| N -> (M %| K + N) = (M %| K) :> bool.
Proof. by rewrite addrC => /dvdmxDr ->. Qed.

Lemma dvdmxBr (m0 m1 m2 : nat)  (N K : 'M_(m2, m1)) (M : 'M[R]_(m0, m1)) :
  M %| N -> (M %| N - K) = (M %| K) :> bool.
Proof. by move=> dvdMN; rewrite dvdmxDr // dvdmxN. Qed.

Lemma dvdmxBl (m0 m1 m2 : nat) (N K : 'M_(m2, m1)) (M : 'M[R]_(m0, m1)) :
  M %| N -> (M %| K - N) = (M %| K) :> bool.
Proof. by move=> dvdMN; rewrite dvdmxDl // dvdmxN. Qed.

Lemma dvdmxB m0 m1 m2 (M : 'M[R]_(m0,m1)) (N K : 'M[R]_(m2,m1)) :
  M %| N -> M %| K -> M %| N - K.
Proof. by move=> /dvdmxBr ->. Qed.

Lemma dvdNmx m0 m1 m2 (M : 'M[R]_(m0,m1)) (N : 'M[R]_(m2,m1)) :
  (- M %| N) = (M %| N).
Proof.
by apply/dvdmxP/dvdmxP=> [] [X ->]; exists (- X); rewrite mulmxN mulNmx ?opprK.
Qed.

Definition ker_mod m0 m1 m2 (M : 'M[R]_(m0,m2)) (N : 'M[R]_(m1,m2)) :=
  rsubmx (ker (col_mx M N)).

Local Notation "M .-ker" := (ker_mod M)
  (at level 10, format "M .-ker") : mxpresentation_scope.

Lemma dvd_ker k m0 m1 m2
  (M : 'M[R]_(m0,m2)) (N : 'M[R]_(m1,m2)) (X : 'M_(k, m1)) :
   (M.-ker N %| X) = (M %| X *m N).
Proof.
apply/dvdmxP/dvdmxP.
  move=> [Y ->]; exists (- (Y *m lsubmx (ker (col_mx M N)))).
  apply/eqP; rewrite mulNmx -addr_eq0 addrC -!mulmxA -mulmxDr -mul_row_col.
  by rewrite hsubmxK kerK mulmx0.
move=> [Y /eqP]; rewrite eq_sym -subr_eq0 -mulNmx -mul_row_col.
move=> /kerP [Z /(congr1 rsubmx)]; rewrite row_mxKr -mulmx_rsub => HZ.
by exists (-Z); rewrite mulNmx -HZ opprK.
Qed.

Lemma dvd_ker_mod_ker m0 m1 m2 (M : 'M[R]_(m0,m2)) (N : 'M[R]_(m1,m2)) :
  (M.-ker N %| ker N).
Proof. by rewrite dvd_ker kerK dvdmx0. Qed.

Lemma dvd_ker_mod_1 m0 m1 m2 (M : 'M[R]_(m0,m2)) (N : 'M[R]_(m1,m2)) :
   (M.-ker N %| 1%:M) = (M %| N).
Proof. by rewrite dvd_ker mul1mx. Qed.

Lemma ker_modK m0 m1 m2 (M : 'M[R]_(m0,m2)) (N : 'M[R]_(m1,m2)) :
   (M %| M.-ker N *m N).
Proof. by rewrite -dvd_ker. Qed.

Lemma ker_mod1 m0 m1 (M : 'M[R]_(m0,m1)) : M %| M.-ker 1%:M.
Proof.
rewrite -dvdNmx; apply/dvdmxP; exists (lsubmx (ker (col_mx M 1%:M))).
apply/eqP; rewrite mulmxN -addr_eq0 addrC -[M.-ker _]mulmx1 -mul_row_col.
by rewrite hsubmxK kerK.
Qed.

Lemma dvd_mx_col k m0 m1 m2
  (M : 'M[R]_(m0,m2)) (N : 'M[R]_(m1,m2)) (X : 'M_(k, m2)) :
   (X %| col_mx M N) = (X %| M) && (X %| N).
Proof.
apply/dvdmxP/andP=> [[Y]|[/dvdmxP [M' ->] /dvdmxP [N' ->]]]; last first.
  by exists (col_mx M' N'); rewrite mul_col_mx.
rewrite -[Y]vsubmxK mul_col_mx => HY.
have := (congr1 usubmx HY, congr1 dsubmx HY).
by rewrite !col_mxKu !col_mxKd => [[-> ->]]; rewrite !dvdmxMl.
Qed.

Lemma dvd_col_mxP k m0 m1 m2
  (M : 'M[R]_(m0,m2)) (N : 'M[R]_(m1,m2)) (X : 'M_(k, m2)) :
   reflect (exists Y, M %| X - Y *m N) (col_mx M N %| X).
Proof.
apply: (iffP (dvdmxP _ _)) => [[Y ->]|[Y /dvdmxP [Z HZ]]]; last first.
  by exists (row_mx Z Y); rewrite mul_row_col -HZ addrNK.
exists (rsubmx Y).
by rewrite -[Y as Y' in Y' *m _]hsubmxK mul_row_col addrK dvdmxMl.
Qed.

Lemma dvd_col_mxl m0 m1 m2 (M : 'M[R]_(m0, m2)) (N : 'M_(m1, m2)) :
  col_mx M N %| N.
Proof. by apply/dvd_col_mxP; exists 1%:M; rewrite mul1mx subrr. Qed.

Lemma dvd_col_mxu m0 m1 m2 (M : 'M[R]_(m0, m2)) (N : 'M_(m1, m2)) :
  col_mx M N %| M.
Proof. by apply/dvd_col_mxP; exists 0; rewrite mul0mx subr0. Qed.

End CoherentRingTheory.

Notation "M .-ker" := (ker_mod M)
  (at level 10, format "M .-ker") : mxpresentation_scope.
Notation "M %| B" := (dvdmx M B) : mxpresentation_scope.

Hint Resolve dvdmx_refl dvdmx0 dvd1mx.


(* It suffices to show how to solve xM = 0 when M is a column for the ring to
   be coherent *)
Section ker_col.

Variable R : comRingType.

Variable dim_ker_col : forall m, 'cV[R]_m -> nat.
Variable ker_col : forall m (M : 'cV[R]_m), 'M[R]_(dim_ker_col M,m).
Hypothesis ker_colP : forall m (M : 'cV_m) (X : 'rV_m),
  reflect (exists Y , X = Y *m ker_col M) (X *m M == 0).

Fixpoint dim_ker_c m n : 'M[R]_(m,n) -> nat :=
  match n return 'M[R]_(m,n) -> nat with
    | S p => fun (M: 'M[R]_(m,1 + _)) =>
       dim_ker_c (ker_col (lsubmx M) *m rsubmx M)
    | _ => fun _ => m
end.

Fixpoint ker_c m n : forall (M : 'M_(m,n)), 'M_(dim_ker_c M,m) := match n with
  | S p => fun (M : 'M_(m,1 + _)) =>
    let G1 := ker_col (lsubmx M) in
    ker_c (G1 *m rsubmx M) *m G1
  | _ => fun _ => 1%:M
  end.

Lemma ker_cP : forall m n (M : 'M[R]_(m,n)) (X : 'rV_m),
  reflect (exists Y, X = Y *m ker_c M) (X *m M == 0).
Proof.
move=> m n; elim: n m=> [n m X | n ih m].
  by rewrite ?thinmx0; apply: (iffP idP)=> //= _; exists X; rewrite mulmx1.
rewrite [n.+1]/(1 + n)%nat => M /=; set G1 := ker_col (lsubmx M).
move: (ih _ (G1 *m rsubmx M))=> {ih} ih X.
apply: (iffP eqP)=> [|[Y hY]];
  rewrite -{1}[M]hsubmxK (@mul_mx_row _ _ _ 1) -(@row_mx0 _ _ 1).
  case/(@eq_row_mx _ _ 1); case/eqP/ker_colP=> V ->; rewrite -mulmxA.
  by case/eqP/ih=> W ->; exists W; rewrite mulmxA.
f_equal; apply/eqP.
  by apply/ker_colP; exists (Y *m ker_c (G1 *m rsubmx M)); rewrite -mulmxA.
by rewrite hY mulmxA -[_ *m rsubmx M]mulmxA; apply/ih; exists Y.
Qed.

End ker_col.

Lemma kerE (R : coherentRingType) m n (M : 'M[R]_(m, n)) :
   ker M = castmx (congr1 _ (col_0mx _), erefl) (0.-ker M).
Proof.
rewrite /(0.-ker) -(esymK (col_0mx _)).
case: _ / (esym (col_0mx _)); rewrite castmx_id.
by apply/matrixP => i j; rewrite mxE /=; congr (ker M _ _); apply: val_inj.
Qed.

(** This section proves that a ring is coherent is the intersection of two *)
(*    finitely generated ideals is again finitely generated. It requires that *)
(*    the underlying ring (in this case a strongly discrete ring) is an *)
(*    integral domain *)
Section IntersectionCoherent.

Variable R : stronglyDiscreteType.

(** The size of the intersection - 1, this is done to ensure that *)
(*    the intersection is nonempty *)
Variable dim_cap : forall m n, 'cV[R]_m -> 'cV[R]_n -> nat.

(** Intersection of two ideals *)
Variable cap :
  forall n m (I : 'cV[R]_n) (J : 'cV[R]_m), 'cV[R]_(dim_cap I J).+1.

Hypothesis cap_spec : forall n m (I : 'cV[R]_n) (J : 'cV[R]_m),
  int_spec (cap I J).

Fixpoint dim_int n : 'cV[R]_n -> nat := match n with
  | 0   => fun _ => 0%N
  | S p => fun (V : 'cV[R]_(1 + p)) =>
               let v  := usubmx V in
               let vs := dsubmx V : 'cV[R]_p in
               ((dim_cap v (-vs)).+1 + dim_int vs)%N
end.

Definition cap_wl n m (I : 'cV_n) (J : 'cV_m) := divid (cap I J) I.

Lemma wl n m (I : 'cV_n) (J : 'cV_m) : cap_wl I J *m I = cap I J.
Proof. by apply: dividK; case: cap_spec. Qed.

Definition cap_wr n m (I : 'cV_n) (J : 'cV_m) := divid (cap I J) J.

Lemma wr n m (I : 'cV_n) (J : 'cV_m) : cap_wr I J *m J = cap I J.
Proof. by apply: dividK; case: cap_spec. Qed.

Fixpoint ker_c_int m : forall (V : 'cV_m),'M_(dim_int V,m) :=
  match m return forall V : 'cV_m, 'M_(dim_int V,m) with
    | 0 => fun _ => 0
    | S p => fun (V' : 'cV_(1 + p)) =>
             let v   := usubmx V' in
             let vs  := dsubmx V' in
             let m0  := ker_c_int vs in
             let wv  := cap_wl v (-vs) in
             let wvs := cap_wr v (-vs) in
             block_mx (if v == 0 then delta_mx 0 0 else wv) (if v == 0 then 0 else wvs)
                      0           m0
  end.

(* TODO: Move to ssrcomplements *)
Lemma colE m n (i : 'I_n) (M : 'M[R]_(m, n)) :
  col i M = M *m delta_mx i 0.
Proof. by apply/trmx_inj; rewrite trmx_mul trmx_delta -rowE tr_col. Qed.

Lemma ker_c_intP : forall m (V : 'cV_m) (X : 'rV_m),
  reflect (exists Y, X = Y *m ker_c_int V) (X *m V == 0).
Proof.
elim => [V X | n IH] /=.
  rewrite thinmx0 flatmx0 /ker_c_int mulmx0.
  apply: (iffP idP) => //= _.
  by exists 0; rewrite mulmx0.
rewrite [n.+1]/(1 + n)%nat => V X.
set v  := usubmx V.
set vs := dsubmx V.
set x  := lsubmx X.
set xs := rsubmx X.
set m0 := ker_c_int vs.
set wv := cap_wl v (-vs).
set wvs := cap_wr v (-vs).
move: (wl v (-vs)); rewrite -/wv => Hwv.
move: (wr v (-vs)); rewrite -/wvs => Hwvs.
rewrite -[V]vsubmxK -[X]hsubmxK.
case v0 : (v == 0).
  apply: (iffP idP) => /= [|[W ->]].
    rewrite (@mul_row_col _ _ 1) -/v (eqP v0) mulmx0 add0r => vs0.
    case: (IH vs xs) => [[A HA]|[]]; last by apply/IH.
    exists (row_mx (const_mx (x 0 0)) A).
    rewrite (@mul_row_block _ _ _ _ 1) -/xs !mulmx0 add0r addr0 -colE col_const HA.
    by f_equal; apply/rowP => i; rewrite !mxE /= !ord1.
  rewrite -mulmxA (@mul_block_col _ _ _ 1) -/v !mul0mx addr0 add0r.
  rewrite -[W]hsubmxK mul_row_col {6}(eqP v0) !mulmx0 add0r mulmxA.
  by apply/IH; exists (rsubmx W).
apply: (iffP idP) => /= [|[W ->]].
  rewrite (@mul_row_col _ _ 1) => hwx.
  have vx00 : ((x * v) 0 0)%:M = x * v.
    by apply/matrixP=> i j; rewrite !ord1 !mxE eqxx.
  have : member ((x * v) 0 0) (cap v (- vs)).
    case: cap_spec => c /= _ _ in_int.
    apply: in_int; first by apply/memberP; exists x; rewrite vx00.
    apply/memberP; exists xs; apply/eqP.
    move: hwx; rewrite -/v -/vs -/x -/xs mulmxN addr_eq0 => /eqP <-.
    by rewrite vx00.
  case/memberP=> W hW.
  case: (IH vs (xs - (W *m wvs))) => [[A HA]|[]].
    exists (row_mx W A).
    rewrite (@mul_row_block _ _ _ _ 1) mulmx0 addr0 -HA addrCA subrr addr0.
    f_equal; apply/(@scalemx_inj _ _ _ (v 0 0)).
    (* The proof breaks down here if strongly discrete rings are not idomains! *)
      apply/negP => v00; case/negP: v0; apply/eqP.
      by apply/rowP => i; rewrite !ord1 /= (eqP v00) !mxE.
    by rewrite -!mul_mx_scalar -mx11_scalar -mulmxA Hwv -hW -/x vx00.
  by apply/IH; rewrite mulmxDl mulNmx addrC -mulmxN -mulmxA Hwvs -hW vx00.
rewrite -[W]hsubmxK (@mul_row_block _ _ _ _ 1) mulmx0 addr0 (@mul_row_col _ _ 1).
rewrite -!mulmxA Hwv addr_eq0 -mulmxN mulmxDl -!mulmxA Hwvs addrC -subr_eq.
rewrite addrN -/vs !mulmxN eq_sym oppr_eq0 mulmxA.
case: (IH vs _) => // [[]].
by exists (rsubmx W).
Qed.

Definition int_coherentMixin := CoherentRing.Mixin (ker_cP ker_c_intP).
Canonical Structure int_coherentType :=
  Eval hnf in CoherentRingType R int_coherentMixin.

End IntersectionCoherent.


(* Using the above result one can prove that Bezout rings are coherent, however
   this is not what we want as we want to prove that constructive PIDs are
   coherent using smith *)
Section BezoutCoherent.

Variable R : bezoutDomainType.

Definition bdim_cap m n (I : 'cV[R]_m) (J : 'cV[R]_n) := 0%N.

Definition bcap m n (I : 'cV_m) (J : 'cV_n) : 'cV[R]_1 :=
  (lcmr (principal_gen I) (principal_gen J))%:M.

Definition bcap_wl m n (I : 'cV_m) (J : 'cV_n) : 'rV[R]_m :=
  let a := principal_gen I in
  let b := principal_gen J in
  (odflt 0 (b %/? gcdr a b))%:M *m principal_w1 I.

Lemma bcap_wlP m n (I : 'cV_m) (J : 'cV_n) : bcap_wl I J *m I = bcap I J.
Proof.
rewrite /bcap_wl /bcap -mulmxA principal_w1_correct mul_scalar_mx.
apply/rowP => i; rewrite !mxE !ord1 {i} /= !mulr1n.
set a := principal_gen _; set b := principal_gen _.
case b0 : (b == 0); first by rewrite (eqP b0) lcm0r mulr0.
case a0 : (a == 0).
  by rewrite (eqP a0) lcmr0 odiv0r /= ?mul0r // gcdr_eq0 b0.
case: odivrP => /= => [x Hx | H].
  apply/(@mulIf _ (gcdr b a)); first by rewrite gcdr_eq0 a0 b0.
  by rewrite mulr_lcm_gcd -mulrA mulrCA -Hx.
case/dvdrP: (dvdr_gcdr b a) => x /eqP Hx.
by move: (H x); rewrite Hx.
Qed.

Definition bcap_wr m n (I : 'cV_m) (J : 'cV_n) : 'rV[R]_n :=
  let a := principal_gen I in
  let b := principal_gen J in
  (odflt 0 (a %/? (gcdr a b)))%:M *m principal_w1 J.

Lemma bcap_wrP n m (I : 'cV_n) (J : 'cV_m) : bcap_wr I J *m J = bcap I J.
Proof.
rewrite /bcap_wl /bcap -mulmxA principal_w1_correct mul_scalar_mx.
apply/rowP => i; rewrite !mxE !ord1 {i} /= !mulr1n.
set b := principal_gen _; set a := principal_gen _.
case a0 : (a == 0); first by rewrite (eqP a0) lcmr0 mulr0.
case b0 : (b == 0).
  by rewrite (eqP b0) lcm0r odiv0r /= ?mul0r // gcdr_eq0 a0 eqxx.
case: odivrP => /= => [x Hx | H].
  apply/(@mulIf _ (gcdr b a)); first by rewrite gcdr_eq0 a0 b0.
  by rewrite -mulrA mulrCA -Hx mulr_lcm_gcd mulrC.
case/dvdrP: (dvdr_gcdl b a) => x /eqP Hx.
by move: (H x); rewrite Hx.
Qed.

Lemma bcap_int (x : 'M_1) (m n : nat) (I : 'cV_m) (J : 'cV_n) :
  (exists I' : 'rV_m, I' *m I = x) ->
  (exists J' : 'rV_n, J' *m J = x) ->
   exists W : 'M_1, W *m bcap I J = x.
Proof.
case => I' HI' [J' HJ'].
move: (principal_w2_correct I).
move: (principal_w2_correct J).
rewrite /bcap /principal.
set a := principal_gen I; set b := principal_gen J => Hb Ha.
have div1 : (a %| x 0 0)%R.
  apply/dvdrP.
  exists ((I' *m principal_w2 I) 0 0).
  move: HI'.
  rewrite -{1}Ha => <-.
  by rewrite mulrC  mul_mx_scalar -scalemxAr !mxE.
have div2 : (b %| x 0 0)%R.
  apply/dvdrP.
  exists ((J' *m principal_w2 J) 0 0).
  move: HJ'.
  rewrite -{1}Hb => <-.
  by rewrite mulrC mul_mx_scalar -scalemxAr !mxE.
move/dvdrP: (dvdr_lcm a b (x 0 0)).
rewrite div1 div2 /= => [[y Hy]].
exists y%:M.
by rewrite -scalar_mxM -Hy -mx11_scalar.
Qed.

(* This is a bit ugly... *)
Lemma bcap_spec m n (I : 'cV[R]_m) (J : 'cV[R]_n) :
  @int_spec _ _ m n I J (bcap I J).
Proof.
split.
- by apply/subidP; exists (bcap_wl I J); rewrite bcap_wlP.
- by apply/subidP; exists (bcap_wr I J); rewrite bcap_wrP.
move=> /= x.
case/memberP => I' hI'.
case/memberP => J' hJ'.
apply/memberP.
have h1 : exists I'0 : 'rV_m, I'0 *m I = x%:M by exists I'.
have h2 : exists J'0 : 'rV_n, J'0 *m J = x%:M by exists J'.
case: (bcap_int h1 h2) => D hD.
by exists D.
Qed.

Definition bezout_coherentMixin := int_coherentMixin bcap_spec.
Canonical Structure bezout_coherentType :=
  Eval hnf in CoherentRingType R bezout_coherentMixin.

End BezoutCoherent.