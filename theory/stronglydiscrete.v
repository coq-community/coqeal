(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice fingroup.
Require Import matrix bigop zmodp mxalgebra poly.

Require Import ssrcomplements dvdring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(** Strongly discrete rings *)
Module StronglyDiscrete.

CoInductive member_spec (R : ringType) n (x : R) (I : 'cV[R]_n)
  : option 'rV[R]_n -> Type :=
| Member J of x%:M = J *m I : member_spec x I (Some J)
| NMember of (forall J, x%:M != J *m I) : member_spec x I None.

Record mixin_of (R : ringType) : Type := Mixin {
  member : forall n, R -> 'cV_n -> option 'rV_n;
  _ : forall n (x : R) (I : 'cV_n), member_spec x I (member x I)
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
Notation stronglyDiscreteType := type.
Notation StronglyDiscreteType T m := (@pack T _ m _ _ id _ id).
Notation StronglyDiscreteMixin := Mixin.
Notation "[ 'stronglyDiscreteType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'stronglyDiscreteType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'stronglyDiscreteType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'stronglyDiscreteType'  'of'  T ]") : form_scope.
End Exports.

End StronglyDiscrete.
Export StronglyDiscrete.Exports.

Definition member R := StronglyDiscrete.member (StronglyDiscrete.class R).
Definition member_spec := StronglyDiscrete.member_spec.

Delimit Scope ideal_scope with IS.

Section StronglyDiscreteTheory.

Variable R : stronglyDiscreteType.

Implicit Types a b c : R.

Lemma member_specP : forall n (x : R) (I : 'cV[R]_n),
  member_spec x I (member x I).
Proof. by case: R => [? [? []]]. Qed.

Lemma memberP n (x : R) (I : 'cV[R]_n) :
  reflect (exists J, x%:M = J *m I) (member x I).
Proof.
case: member_specP=> /= [J ->|h]; first by apply: ReflectT; exists J.
apply: ReflectF=> [[J hJ]].
by move: (h J); rewrite hJ eqxx.
Qed.

(** Ideal theory of strongly discrete rings *)
Section IdealTheory.

(** The sub-ideal membership function *)
Definition subid m n (I : 'cV[R]_m) (J : 'cV[R]_n) : bool :=
  [forall i, member (I i 0) J].

Arguments Scope subid
  [nat_scope nat_scope ideal_scope ideal_scope].
Prenex Implicits subid.
Local Notation "A <= B" := (subid A B) : ideal_scope.
Local Notation "A <= B <= C" := ((A <= B) && (B <= C))%IS : ideal_scope.
Local Notation "A == B" := (A <= B <= A)%IS : ideal_scope.

Lemma subidP m n (I : 'cV[R]_m) (J : 'cV[R]_n) :
  reflect (exists D, I = D *m J) (I <= J)%IS.
Proof.
apply: (iffP (\forall_(memberP _ _))); last first.
  move=> [D ->] i; exists (row i D).
  apply/matrixP => i' j'; rewrite !ord1 {i' j'} !mxE /=.
  by apply: eq_bigr => l _; rewrite !mxE.
move=> HJ; pose M i j := projT1 (sig_eqW (HJ i)) 0 j.
exists (\matrix_(i,j) M i j); apply/colP => i; rewrite mxE.
transitivity (\sum_j M i j * J j 0); last first.
  by apply: eq_bigr => j _ /=; rewrite mxE.
rewrite /M {M}; case: sig_eqW => //= K.
by move=> /matrixP /(_ 0 0); rewrite !mxE eqxx mulr1n.
Qed.

Definition divid m n (I : 'cV[R]_m) (J : 'cV[R]_n) : 'M_(m, n):=
  if subidP I J is ReflectT P then projT1 (sig_eqW P) else 0.

Lemma dividK m n (I : 'cV[R]_m) (J : 'cV[R]_n) :
  (I <= J)%IS -> divid I J *m J = I.
Proof. by rewrite /divid; case: subidP => //= p; case: sig_eqW. Qed.

Lemma memberE m (I : 'cV[R]_m) (a : R) :
  member a I = (a%:M <= I)%IS :> bool.
Proof. by apply/memberP/subidP. Qed.

Lemma subid_colP m n (I : 'cV[R]_m) (J : 'cV[R]_n) :
  reflect (forall i, (I i 0)%:M <= J)%IS (I <= J)%IS.
Proof. by apply: (iffP forallP) => H i; rewrite (=^~memberE, memberE). Qed.

Lemma subid_refl m (I : 'cV[R]_m) : (I <= I)%IS.
Proof. by apply/subidP; exists 1%:M; rewrite mul1mx. Qed.
Hint Resolve subid_refl.

Lemma subrid m i (I : 'cV[R]_m) : ((I i 0)%:M <= I)%IS.
Proof.
apply/subidP; exists (delta_mx 0 i); rewrite -rowE.
by apply/colP=> j; rewrite !mxE ord1 mulr1n.
Qed.
Hint Resolve subrid.

(** Obsolete *)
Remark member_in m x (I : 'cV[R]_m) : (exists i, I i 0 = x) -> member x I.
Proof. by case=> i <-; rewrite memberE subrid. Qed.

Lemma sub0id n m (I : 'cV[R]_m) : ((0 : 'cV_n) <= I)%IS.
Proof. by apply/subidP; exists 0; rewrite mul0mx. Qed.
Hint Resolve sub0id.

Lemma subid1 m (I : 'cV[R]_m) : (I <= 1)%IS.
Proof. by apply/subidP; exists I; rewrite mulmx1. Qed.
Hint Resolve subid1.

Lemma subidMl m n p (I : 'cV[R]_m) (J : 'cV[R]_n) (D : 'M_(p, _)) :
      (I <= J)%IS -> (D *m I <= J)%IS.
Proof.
by move=> /subidP [I' ->]; apply/subidP; exists (D *m I'); rewrite mulmxA.
Qed.

Lemma subid_trans n m p (J : 'cV[R]_n) (I : 'cV[R]_m) (K : 'cV[R]_p) :
   (I <= J)%IS -> (J <= K)%IS -> (I <= K)%IS.
Proof. by move=> /subidP [I' ->] /subidP [J' ->]; rewrite mulmxA subidMl. Qed.

Lemma subid_le0 m n (I : 'cV[R]_n) : (I <= (0 : 'cV_m))%IS = (I == 0).
Proof.
apply/subidP/eqP => [[D ->]|->]; first by rewrite mulmx0.
by exists 0; rewrite mul0mx.
Qed.

Lemma eqid_eq0 m n (I : 'cV[R]_n) : (I == (0 : 'cV_m))%IS = (I == 0).
Proof. by rewrite subid_le0 sub0id andbT. Qed.

(* Obsolete *)
Remark member_subid m n x (I : 'cV[R]_m) (J : 'cV[R]_n) :
  member x I -> (I <= J)%IS -> member x J.
Proof. by rewrite !memberE; apply: subid_trans. Qed.

Remark subid_memberP m n (I : 'cV[R]_m) (J : 'cV[R]_n) :
  reflect (forall x, member x I -> member x J) (I <= J)%IS.
Proof.
apply: (iffP idP); first by move=> leIJ i; rewrite !memberE => /subid_trans ->.
move=> HIJ; apply/subid_colP => i.
by have := (HIJ (I i 0)); rewrite !memberE; apply.
Qed.

(** Theory of subid and eqid *)

Definition eqid m n (I : 'cV[R]_m) (J : 'cV[R]_n) :=
  forall p (K : 'cV[R]_p), (((I <= K)%IS = (J <= K)%IS)
                          * ((K <= I)%IS = (K <= J)%IS))%type.
Local Notation "I :=: J" := (eqid I J)%IS : ideal_scope.

Lemma eqidP m n (I : 'cV[R]_m) (J : 'cV[R]_n) :
  reflect (I :=: J)%IS (I == J)%IS.
Proof.
apply: (iffP andP) => [[sIJ sJI] p K | eqIJ]; last by rewrite !eqIJ.
by split; apply/idP/idP; by [move/subid_trans->|move/(subid_trans _)->].
Qed.

Lemma subeqid_refl m (I : 'cV[R]_m) : (I == I)%IS.
Proof. by rewrite !subid_refl. Qed.
Hint Resolve subeqid_refl.

Lemma eqid_refl m (I : 'cV[R]_m) : (I :=: I)%IS.
Proof. exact/eqidP. Qed.
Hint Resolve eqid_refl.

Lemma eqid_sym m n (I: 'cV[R]_n) (J: 'cV[R]_m) : (I :=: J)%IS -> (J :=: I)%IS.
Proof. by move=> /eqidP; rewrite andbC => /eqidP. Qed.

Lemma eqid_trans m n k (J : 'cV_n) (I : 'cV[R]_m) (K : 'cV_k) :
  (I :=: J -> J :=: K -> I :=: K)%IS.
Proof. by move=> IJ JK; apply/eqidP; rewrite !IJ !JK. Qed.

Lemma subid_castmxl m n p (I : 'cV[R]_m) (J : 'cV[R]_n) (h : m = p):
  ((castmx (h,erefl _) I) <= J)%IS = (I <= J)%IS.
Proof. by case: _ / h. Qed.

Lemma subid_castmxr m n p (I : 'cV[R]_m) (J : 'cV[R]_n) (h : n = p):
  (I <= (castmx (h,erefl _) J))%IS = (I <= J)%IS.
Proof. by case: _ / h. Qed.

(** Ideal addition *)

Definition addid m n (I : 'cV[R]_m) (J : 'cV[R]_n) := col_mx I J.

Local Notation "I +i J" := (addid I J) (at level 30).

Lemma sub_add0rid m n (I : 'cV[R]_m) : (I +i (0 : 'cV[R]_n) <= I)%IS.
Proof.
apply/subidP; exists (pid_mx m).
by rewrite pid_mx_col mul_col_mx mul1mx mul0mx.
Qed.

Lemma sub_addid0r m n (I : 'cV[R]_m) : (I <= I +i (0 : 'cV[R]_n))%IS.
Proof.
apply/subidP; exists (pid_mx m).
by rewrite pid_mx_row mul_row_col mul1mx mulmx0 addr0.
Qed.

 Lemma subid_addC m n (I : 'cV[R]_m) (J : 'cV[R]_n) :
  (I +i J <= J +i I)%IS.
Proof.
apply/subidP; exists (block_mx 0 1%:M 1%:M 0).
by rewrite mul_block_col !(mul0mx,mul1mx) addr0 add0r.
Qed.

Lemma subid_addAl m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p) :
  (I +i (J +i K) <= (I +i J) +i K)%IS.
Proof.
apply/subidP.
exists (block_mx (row_mx 1%:M 0) 0 (block_mx 0 1%:M 0 0) (col_mx 0 1%:M)).
rewrite !mul_block_col mul_row_col mul_col_mx add_col_mx.
by rewrite !(mul0mx,mul1mx,add0r,addr0).
Qed.

Lemma subid_addAr m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p) :
  ((I +i J) +i K <= I +i (J +i K))%IS.
Proof.
apply/subidP.
exists (block_mx (col_mx 1%:M 0) (block_mx 0 0 1%:M 0) 0 (row_mx 0 1%:M)).
rewrite !mul_block_col mul_row_col mul_col_mx add_col_mx.
by rewrite !(mul0mx,mul1mx,add0r,addr0).
Qed.

Lemma sub_add0lid m n (I : 'cV[R]_n) : ((0 : 'cV[R]_m) +i I <= I)%IS.
Proof. exact: (subid_trans (subid_addC 0 I) (sub_add0rid m I)). Qed.

Lemma sub_addid0l m n (I : 'cV[R]_n) : (I <= (0 : 'cV[R]_m) +i I)%IS.
Proof. exact: (subid_trans (sub_addid0r _ _) (subid_addC I 0)). Qed.

Lemma addid0 m n (I : 'cV[R]_m) : (I +i (0 : 'cV[R]_n) :=: I)%IS.
Proof. by apply/eqidP; rewrite sub_addid0r sub_add0rid. Qed.

Lemma add0id m n (I : 'cV[R]_m) : ((0 : 'cV[R]_n) +i I :=: I)%IS.
Proof. by apply/eqidP; rewrite sub_addid0l sub_add0lid. Qed.

Lemma addidC m n (I : 'cV[R]_m) (J : 'cV[R]_n) : (I +i J :=: J +i I)%IS.
Proof. by apply/eqidP; rewrite !subid_addC. Qed.

Lemma addid_addA m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p):
  (I +i (J +i K) :=: (I +i J) +i K)%IS.
Proof. by apply/eqidP; rewrite subid_addAl subid_addAr. Qed.

Lemma sub_addidl m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p):
  (J <= K)%IS -> (I +i J <= I +i K)%IS.
Proof.
case/subidP => D hD; apply/subidP.
exists (block_mx 1%:M 0 0 D).
by rewrite hD mul_block_col mul1mx !mul0mx addr0 add0r.
Qed.

Lemma sub_addidr m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p):
  (J <= K)%IS -> (J +i I <= K +i I)%IS.
Proof.
case/subidP => D hD; apply/subidP.
exists (block_mx D 0 0 1%:M).
by rewrite hD mul_block_col mul1mx !mul0mx addr0 add0r.
Qed.

Lemma add_addil m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p) :
  (J :=: K)%IS -> (I +i J :=: I +i K)%IS.
Proof. by move=> eqJK; apply/eqidP; rewrite ?sub_addidl ?eqJK. Qed.

Lemma add_addir m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p) :
  (J :=: K)%IS -> (J +i I :=: K +i I)%IS.
Proof. by move=> eqJK; apply/eqidP; rewrite ?sub_addidr ?eqJK. Qed.

Lemma subid_addid_congr m n p (I : 'cV[R]_n) (J : 'cV[R]_m) (K : 'cV[R]_p) :
  (I <= K)%IS -> (J <= K)%IS -> (I +i J <= K)%IS.
Proof.
case/subidP => C hC /subidP [D hD]; apply/subidP.
by exists (col_mx C D); rewrite mul_col_mx -hC -hD.
Qed.

Lemma addid_congr m n p o (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p) (L : 'cV_o) :
  (I <= K -> J <= L -> I +i J <= K +i L)%IS.
Proof.
case/subidP => X hX; case/subidP => Y hY; apply/subidP.
exists (block_mx X 0 0 Y).
by rewrite mul_block_col !mul0mx addr0 add0r hX hY.
Qed.

Lemma scale_addid (x: R) m n (I : 'cV[R]_m) (J: 'cV[R]_n):
  x *: (I +i J) = (x *: I) +i (x *: J).
Proof. by rewrite /addid -scale_col_mx. Qed.

Lemma subid_scaleid (x: R) m n (I: 'cV[R]_m) (J: 'cV[R]_n):
  x != 0 -> (I <= J)%IS = (x *: I <= x *: J)%IS.
Proof.
move=> x0.
apply/idP/idP; case/subidP => D hD; apply/subidP; exists D.
  by rewrite hD scalemxAr.
by apply/eqP; rewrite -(inj_eq (scalemx_inj x0)) scalemxAr hD.
Qed.

Lemma eqid_scaleid (x: R) m n (I: 'cV[R]_m) (J: 'cV[R]_n):
  x != 0 -> (I == J)%IS = (x *: I == x *: J)%IS.
Proof.
move=> x0; apply/idP/andP=> [|[]].
  by rewrite (@subid_scaleid x) //; case/andP=> ->; rewrite (@subid_scaleid x).
by rewrite -(@subid_scaleid x) // => ->; rewrite -(@subid_scaleid x) // => ->.
Qed.

(** Ideal multiplication *)
(* This is a bit problematic as mxvec gives a row vector... *)
Definition mulid m n (I : 'cV[R]_m) (J : 'cV[R]_n) : 'cV[R]_(m * n) :=
  (mxvec (I *m J^T))^T.

Local Notation "I *i J" := (mulid I J) (at level 50).

Lemma subid_tr_mxvec m n (I : 'M[R]_(m,n)) : ((mxvec I)^T <= (mxvec I^T)^T)%IS.
Proof.
apply/subid_colP => i /=; case: (mxvec_indexP i) => {i} i j.
by rewrite (subid_trans _ (subrid (mxvec_index j i) _)) // !(mxE, mxvecE).
Qed.

Lemma eqid_tr_mxvec m n (I : 'M[R]_(m,n)) : ((mxvec I)^T :=: (mxvec I^T)^T)%IS.
Proof.
by apply/eqidP; rewrite -[I in X in _ && (_ <= X)%IS]trmxK !subid_tr_mxvec.
Qed.

(* Lemma mxvec_r1l m (I: 'cV[R]_m) : (mxvec I <= I)%IS. *)
(* Proof. *)
(* apply/subid_in => i. *)
(* case/mxvec_indexP : i => i j; rewrite !ord1 {i}. *)
(* rewrite mxvecE. *)
(* by exists j. *)
(* Qed. *)

(* Lemma mxvec_r1r m (I: 'cV[R]_m) : (I <= mxvec I)%IS. *)
(* Proof. *)
(* apply/subid_in => i. *)
(* exists (mxvec_index 0 i). *)
(* by rewrite mxvecE. *)
(* Qed. *)

Lemma mxvec0 (V : zmodType) (m n : nat) : mxvec (0 : 'M[V]_(m, n)) = 0.
Proof. by apply/eqP; rewrite mxvec_eq0. Qed.

Lemma trmx_eq0 (V : zmodType) (m n : nat) (A : 'M[V]_(m, n)) :
   (A^T == 0) = (A == 0).
Proof. by rewrite -trmx0 (inj_eq (can_inj (@trmxK _ _ _))). Qed.

Lemma mulid0 m n (I: 'cV[R]_m) : I *i (0: 'cV[R]_n) = 0.
Proof. by rewrite /mulid trmx0 mulmx0 mxvec0 trmx0. Qed.

Lemma subid_mulC m n (I : 'cV[R]_m) (J : 'cV[R]_n) : (I *i J <= J *i I)%IS.
Proof. by rewrite (subid_trans (subid_tr_mxvec _)) // trmx_mul trmxK. Qed.

Lemma mulidC m n (I : 'cV[R]_m) (J : 'cV[R]_n) : (I *i J :=: J *i I)%IS.
Proof. by apply/eqidP; rewrite !subid_mulC. Qed.

Lemma sub_mulidl m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p):
  (J <= K -> I *i J <= I *i K)%IS.
Proof.
case/subidP => D hD; apply/subidP; exists (lin_mulmxr D^T)^T.
rewrite -trmx_mul; apply: (canLR (@trmxK _ _ _)); apply: (canLR vec_mxK).
by rewrite trmxK mx_vec_lin /= hD trmx_mul mulmxA.
Qed.

Lemma sub_mulidr m n p (I: 'cV[R]_m) (J: 'cV[R]_n) (K: 'cV[R]_p) :
  (J <= K -> J *i I <= K *i I)%IS.
Proof. by move=> h; rewrite mulidC (mulidC _ _ _).2 sub_mulidl. Qed.

Lemma eqid_mulidAl l m n (K : 'cV[R]_l) (I : 'cV[R]_m) (J : 'cV[R]_n) :
  (I *i (J *i K) :=: (I *i J) *i K)%IS.
Proof.
rewrite /mulid; apply/eqidP/andP; split; apply/subid_colP => i;
case/mxvec_indexP : i => i j; rewrite !(mxE, mxvecE, big_ord1).
  case/mxvec_indexP : j => j k; rewrite !(mxE, mxvecE, big_ord1).
  rewrite (subid_trans _ (subrid (mxvec_index (mxvec_index i j) k) _)) //.
  by rewrite !(mxE, mxvecE, big_ord1) mulrA.
case/mxvec_indexP : i => i k; rewrite !(mxE, mxvecE, big_ord1).
rewrite (subid_trans _ (subrid (mxvec_index i (mxvec_index k j)) _)) //.
by rewrite !(mxE, mxvecE, big_ord1) mulrA.
Qed.

Lemma mulid_addidr m n k (I : 'cV[R]_m) (J : 'cV[R]_n) (K : 'cV[R]_k) :
  (I *i (J +i K) <= (I *i J) +i (I *i K))%IS.
Proof.
apply/forallP=> /= i.
apply: member_in.
case/mxvec_indexP: i => i x.
rewrite mxE mxvecE !mxE big_ord1 !mxE.
case: splitP => j hj.
  exists (lshift (m*k)%nat (mxvec_index i j)).
  rewrite !mxE.
  case: splitP => ij /= hij.
    case/mxvec_indexP : ij hij => a b /= hab.
    have : enum_rank (i,j) = enum_rank (a,b) by apply/ord_inj.
    case/enum_rank_inj => -> ->.
    by rewrite mxE mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
  case/mxvec_indexP : ij hij => a b /= hab.
  have : ~ (enum_rank (i,j) < (m * n)%nat)
    by rewrite hab -{2}[(m * n)%nat]addn0 ltn_add2l ltn0.
  case.
  by apply (leq_trans (ltn_ord _)); rewrite /= eq_card_prod // !card_ord.
exists (rshift (m*n)%nat (mxvec_index i j)).
rewrite !mxE.
case: splitP => ij /= hij.
  case/mxvec_indexP : ij hij => a b /= hab.
  have : ~ (enum_rank (a,b) < (m * n)%nat)
    by rewrite -hab -{2}[(m * n)%nat]addn0 ltn_add2l ltn0.
  case.
  by apply (leq_trans (ltn_ord _)); rewrite /= eq_card_prod // !card_ord.
case/mxvec_indexP : ij hij => a b /= hab.
have : enum_rank (i,j) = enum_rank (a,b).
  apply/ord_inj/eqP.
  by rewrite -(eqn_add2l (m * n)%nat) hab.
case/enum_rank_inj => -> ->.
by rewrite mxE mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
Qed.

Lemma scale_mxvec a m n (M : 'M[R]_(m,n)) : a *: mxvec M = mxvec (a *: M).
Proof.
apply/matrixP=> i j; rewrite mxE ord1 {i}.
by case/mxvec_indexP: j=> i j; rewrite !mxvecE mxE.
Qed.

Lemma scale_trmx a m n (M : 'M[R]_(m,n)) : a *: M^T = (a *: M)^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma scale_mulidr a n m (I : 'cV[R]_n) (J : 'cV[R]_m) :
  (a *: (I *i J) :=: (a *: I) *i J)%IS.
Proof. by rewrite scale_trmx scale_mxvec -!mul_scalar_mx /mulid -mulmxA. Qed.

Lemma subid_mulid_congr m n p o
  (I : 'cV[R]_m) (J : 'cV[R]_n) (K : 'cV[R]_p) (L : 'cV_o) :
  (I <= K)%IS -> (J <= L)%IS -> (I *i J <= K *i L)%IS.
Proof.
move => h1 h2.
by apply/(subid_trans (sub_mulidl _ h2))/(sub_mulidr _ h1).
Qed.

Lemma mulid_congr m n p q (I: 'cV[R]_m) (J: 'cV[R]_n)
  (K: 'cV[R]_p) (L: 'cV[R]_q) :
  (I :=: K)%IS -> (J :=: L)%IS -> (I *i J :=: K *i L)%IS.
Proof.
case/eqidP/andP=> h1 h2 /eqidP /andP [h3 h4]; apply/eqidP/andP; split.
  by apply/(subid_trans (sub_mulidl _ h3))/(sub_mulidr _ h1).
by apply/(subid_trans (sub_mulidl _ h4))/(sub_mulidr _ h2).
Qed.

(* Lemma scaleidE m a (I: 'cV[R]_m) : (a *: I == (a%:M : 'M[R]_1) *i I)%IS. *)
(* Proof. *)
(* rewrite /mulid tr_scalar_mx mul_scalar_mx scale_mxvec. *)
(* case ha : (a == 0). *)
(* - rewrite (eqP ha) !scale0r. *)
(*   by apply/andP; split; apply/subidP; exists 0; rewrite mul0mx. *)
(* by rewrite -eqid_scaleid ?mxvec_r1l ?mxvec_r1r // ha. *)
(* Qed. *)

(* (** A version of mxvec and ideal multiplication that is more suitable for *)
(*    implementation as a computable version *) *)
(* Fixpoint flattenmx m n : 'M[R]_(m,n) -> 'cV[R]_(m * n) := *)
(*   match m return 'M[R]_(m,n) -> 'cV[R]_(m * n) with *)
(*   | O => fun _ => 0 *)
(*   | S p => fun (M : 'M[R]_(1 + p,n)) => row_mx (usubmx M) (flattenmx (dsubmx M)) *)
(*   end. *)

(* (** Every element in flattenmx is in mxvec *) *)
(* Lemma flattenmx_in_mxvec : forall m n (M : 'M[R]_(m,n)) i, *)
(*   exists j, ((mxvec M) 0 j = (flattenmx M) 0 i). *)
(* Proof. *)
(* elim => [n M []|m ih n] //. *)
(* rewrite [m.+1]/(1 + m)%N => M i /=. *)
(* rewrite !mxE. *)
(* case: splitP => j hj. *)
(*   exists (mxvec_index 0 j). *)
(*   by rewrite mxvecE !mxE lshift0. *)
(* case: (ih _ (dsubmx M) j) => k hk. *)
(* case/mxvec_indexP: k hk => a b. *)
(* rewrite mxvecE !mxE rshift1 => hh. *)
(* exists (mxvec_index (lift 0 a) b). *)
(* by rewrite mxvecE. *)
(* Qed. *)

(* Lemma flattenmx_mxvec m n (M : 'M[R]_(m,n)) : (flattenmx M <= mxvec M)%IS. *)
(* Proof. by apply/subid_in/flattenmx_in_mxvec. Qed. *)

(* (** Build the correct index in flattenmx *) *)
(* Lemma flattenmx_index_proof (m n : nat) : forall (i : 'I_m) (j : 'I_n), *)
(*   (i * n + j < m * n)%N. *)
(* Proof. *)
(* move=> [i hi] [j hj] /=. *)
(* case: m hi => //= m; rewrite ltnS => hi. *)
(* case: n hj => //= n; rewrite ltnS => hj. *)
(* rewrite !mulSn !mulnS addSn ltnS -addnA [(n + _)%N]addnCA. *)
(* apply: leq_add => //; rewrite addnC. *)
(* by apply: leq_add => //; rewrite leq_mul2r hi orbT. *)
(* Qed. *)

(* Definition flattenmx_index (m n : nat) (i : 'I_m) (j : 'I_n) := *)
(*   Ordinal (flattenmx_index_proof i j). *)

(* Lemma flattenmx_indexE : forall m n (M : 'M[R]_(m,n)) (i : 'I_m) (j : 'I_n), *)
(*   (flattenmx M) 0 (flattenmx_index i j) = M i j. *)
(* Proof. *)
(* elim => [m M []|] //. *)
(* rewrite /flattenmx_index /= => m ih n. *)
(* rewrite [m.+1]/(1 + m)%N => M i j. *)
(* rewrite -{3}[M]vsubmxK !mxE. *)
(* case: splitP => /= k hk. *)
(*   case: splitP => /= l hl. *)
(*     rewrite ord1 !mxE lshift0. *)
(*     move: hk. *)
(*     by rewrite hl ord1 mul0n add0n => /ord_inj ->. *)
(*   case: k hk => /= k hk h. *)
(*   suff hnk : n <= k by move: (leq_ltn_trans hnk hk); rewrite ltnn. *)
(*   move: h. *)
(*   by rewrite hl mulnDl mul1n => <-; rewrite -{1}[n]addn0 -addnA leq_add2l. *)
(* case: splitP => l hl. *)
(*   rewrite hl !ord1 mul0n add0n in hk. *)
(*   case: j hk => /= j hj hk. *)
(*   move: hj; rewrite hk => hj. *)
(*   suff : (n + k < n) -> false by move => /(_ hj). *)
(*   by rewrite -ltn_subRL subnn. *)
(* move: (ih _ (dsubmx M) l j); rewrite !mxE => <-. *)
(* f_equal; apply/ord_inj => /=. *)
(* move: hk; rewrite hl mulnDl mul1n -addnA => /eqP. *)
(* by rewrite eqn_add2l => /eqP ->. *)
(* Qed. *)

(* (** Every element in mxvec is in flattenmx *) *)
(* Lemma mxvec_in_flattenmx m n (M : 'M[R]_(m,n)) i : *)
(*   exists j, ((flattenmx M) 0 j = (mxvec M) 0 i). *)
(* Proof. *)
(* case/mxvec_indexP: i => i j; rewrite mxvecE. *)
(* exists (flattenmx_index i j). *)
(* by rewrite flattenmx_indexE. *)
(* Qed. *)

(* Lemma mxvec_flattenmx m n (M : 'M[R]_(m,n)) : (mxvec M <= flattenmx M)%IS. *)
(* Proof. by apply/subid_in/mxvec_in_flattenmx. Qed. *)

(* (** The inverse of flattenmx_index *) *)
(* Lemma flattenmx_indexP m n (k : 'I_(m * n)) : exists i j, *)
(*   k = flattenmx_index i j. *)
(* Proof. *)
(* have n0 : 0 < n by case: n k => // [[l]]; rewrite muln0. *)
(* have h1 : (k %/ n < m) by rewrite ltn_divLR. *)
(* have h2 : (k %% n < n) by rewrite ltn_mod. *)
(* exists (Ordinal h1); exists (Ordinal h2). *)
(* apply/ord_inj => /=. *)
(* exact: (divn_eq k n). *)
(* Qed. *)

(* (** Alternative version of ideal multiplication that is more suitable *)
(*    for computation as the behavior is more predictable than the one *)
(*    based on mxvec *) *)
(* Definition mulidc m n (I : 'cV[R]_m) (J : 'cV[R]_n) := flattenmx (I^T *m J). *)

(* Lemma mulidcP m n (I : 'cV[R]_m) (J : 'cV[R]_n) : (I *i J == mulidc I J)%IS. *)
(* Proof. *)
(* by apply/andP; split; rewrite /mulid /mulidc ?mxvec_flattenmx ?flattenmx_mxvec. *)
(* Qed. *)

(* (** Every element in mulidc is in mulid *) *)
(* Lemma mulidc_in_mulid m n (I : 'cV[R]_m) (J : 'cV[R]_n) i : *)
(*   exists j, ((I *i J) 0 j = (mulidc I J) 0 i). *)
(* Proof. by rewrite /mulid /mulidc; apply/flattenmx_in_mxvec. Qed. *)

(* (* Special lemma that is just here for the computable version of ideal *)
(*    intersection in prufer domains... *) *)

(* Lemma mulidc_in_mulid2 : forall m n l (I : 'cV[R]_m) (J : 'cV[R]_n) (K : 'cV[R]_l) i, *)
(*   exists j, (((I *i J) *i K) 0 j = (mulidc (mulidc I J) K) 0 i). *)
(* Proof. *)
(* have temp : forall m n l (I : 'cV[R]_m) (J : 'cV[R]_n) (K : 'cV[R]_l) i, *)
(*            (forall i, exists j, I 0 j = K 0 i) -> *)
(*             exists j, ((I *i J) 0 j = (mulidc K J) 0 i). *)
(*   move=> m n l I J K i. *)
(*   case: (flattenmx_indexP i) => a [b ->] /(_ a) [x hx]. *)
(*   exists (mxvec_index x b). *)
(*   rewrite /mulidc flattenmx_indexE mxvecE !mxE. *)
(*   apply: eq_big => // c _. *)
(*   by rewrite !mxE ord1 hx. *)
(* move=> m n l I J K i. *)
(* apply: temp => j. *)
(* case: (mulidc_in_mulid I J j) => k hk. *)
(* by exists k; rewrite hk. *)
(* Qed. *)


(** Ideal intersection *)

Section IdealIntersection.

Variable cap_size : forall n m, 'cV[R]_n -> 'cV[R]_m -> nat.

CoInductive int_spec m n (I : 'cV[R]_m) (J : 'cV[R]_n) : 'cV[R]_(cap_size I J).+1 -> Type :=
  IntSpec cap of (cap <= I)%IS
  & (cap <= J)%IS
  & (forall x, member x I -> member x J -> member x cap) : int_spec cap.

End IdealIntersection.

End IdealTheory.

End StronglyDiscreteTheory.

Notation "A <= B" := (subid A B) : ideal_scope.
Notation "A <= B <= C" := ((subid A B) && (subid B C)) : ideal_scope.
Notation "A == B" := ((subid A B) && (subid B A)) : ideal_scope.
Notation "I +i J" := (addid I J) (at level 30).
Notation "I *i J" := (mulid I J) (at level 50).

Section BezoutStronglyDiscrete.

Variable R : bezoutDomainType.

Definition bmember n (x : R) (I : 'cV[R]_n) := match x %/? principal_gen I with
  | Some a => Some (a %:M *m principal_w1 I)
  | None   => None
end.

Lemma bmember_correct : forall n (x : R) (I : 'cV[R]_n),
  member_spec x I (bmember x I).
Proof.
rewrite /bmember => n x I.
case: odivrP => [a | ] Ha /=; constructor.
  by rewrite -mulmxA principal_w1_correct Ha scalar_mxM.
move => J.
rewrite -(principal_w2_correct I) /principal mulmxA scalar_mxC.
move: (Ha ((J *m principal_w2 I) 0 0)).
apply/contra.
rewrite {1}[J *m principal_w2 I]mx11_scalar -scalar_mxM.
move/eqP/matrixP => /(_ 0 0).
rewrite !mxE /= !mulr1n => ->.
by rewrite mulrC.
Qed.

Definition bezout_stronglyDiscreteMixin := StronglyDiscrete.Mixin bmember_correct.
Canonical Structure bezout_stronglyDiscreteType :=
  Eval hnf in StronglyDiscreteType R bezout_stronglyDiscreteMixin.

End BezoutStronglyDiscrete.
Hint Resolve subid_refl sub0id subid1.
