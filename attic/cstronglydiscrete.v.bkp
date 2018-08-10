Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice fingroup.
Require Import matrix bigop zmodp mxalgebra poly.

Require Import stronglydiscrete ssrcomplements dvdring cssralg cdvdring.
Require Import seqmatrix.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** "Computable" Strongly discrete rings *)
Module CStronglyDiscrete.

Record mixin_of (R : stronglyDiscreteType) (CR : cringType R) : Type := Mixin {
  cmember : nat -> CR -> seqmatrix CR -> option (seqmatrix CR);
  _ : forall n x (I : 'rV[R]_n),
        omap trans (member x I) = cmember n (trans x) (trans I)
}.

Section ClassDef.

Variable R : stronglyDiscreteType.
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

Notation cstronglyDiscreteType R := (@type _ (Phant R)).
Notation CStronglyDiscreteType R m := (@pack _ (Phant R) _ _ m _ _ id _ id).
Notation CStronglyDiscreteMixin := Mixin.
Notation "[ 'cstronglyDiscreteType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'cstronglyDiscreteType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'cstronglyDiscreteType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'cstronglyDiscreteType' T 'of'  V ]") : form_scope.
End Exports.

End CStronglyDiscrete.

Export CStronglyDiscrete.Exports.

Definition cmember (R : stronglyDiscreteType) (CR : cstronglyDiscreteType R) :=
  CStronglyDiscrete.cmember (CStronglyDiscrete.class CR).

Section CStronglyDiscreteTheory.

Variable R : stronglyDiscreteType.
Variable CR : cstronglyDiscreteType R.

Lemma cmemberE : forall n x (I : 'rV[R]_n),
  omap trans (member x I) = cmember n (@trans _ CR x) (trans I).
Proof. by case: CR => [? [? []]]. Qed.

(* (* The sub-ideal membership function *) *)
(* Fixpoint subid m n : 'rV[R]_m -> 'rV[R]_n -> bool := *)
(*   match m return 'rV[R]_m -> 'rV[R]_n -> bool with *)
(*     | S p => fun (I : 'rV[R]_(1 + _)) J => *)
(*           member (I 0 0) J && subid (rsubmx I) J *)
(*     | _ => fun _ _ => true *)
(*   end. *)

(** A function that explicitly computes the witness *)
Fixpoint csubidW m n (I : seqmatrix CR) (J : seqmatrix CR) :=
  match m with
    | S p => match cmember n (I O O) J with
      | Some w => row_seqmx w (csubidW p n (rsubseqmx 1 I) J)
      | None   => seqmx0 CR n m
      end
    | _ => seqmx0 CR n O
  end.

Lemma csubidWE : forall m n (I : 'rV[R]_m) (J : 'rV[R]_n),
  seqmx_of_mx CR (subidW I J) = csubidW m n (trans I) (trans J).
Proof.
elim => [n I J |m ih] /=; first by rewrite seqmx0E.
rewrite [m.+1]/(1 + m)%N => n I J /=.
rewrite (seqmxE CR I 0 0).
case: member (cmemberE (I 0 0) J) => /= [a <- | <- ]; last by rewrite seqmx0E.
by rewrite -(row_seqmxE CR a) ih rsubseqmxE.
Qed.

Fixpoint cflattenmx m (M : seqmatrix CR) := match m with
  | O => seqmx0 CR 1 0
  | S p => row_seqmx (usubseqmx 1 M) (cflattenmx p (dsubseqmx 1 M))
  end.

Lemma cflattenmxE : forall m n (M : 'M[R]_(m,n)),
  cflattenmx m (seqmx_of_mx CR M) = seqmx_of_mx CR (flattenmx M).
Proof.
elim=> [n M|m ih n]; first by rewrite flatmx0 /= !seqmx0E /=.
rewrite [m.+1]/(1 + m)%N => M /=.
by rewrite usubseqmxE dsubseqmxE ih row_seqmxE.
Qed.

Definition cmulidc m n (I : seqmatrix CR) (J : seqmatrix CR) :=
  cflattenmx m (mulseqmx 1 n (trseqmx I) J).

Lemma cmulidcE m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  cmulidc m n (seqmx_of_mx CR I) (seqmx_of_mx CR J) =
  seqmx_of_mx CR (mulidc I J).
Proof. by rewrite /cmulidc /mulidc -cflattenmxE -mulseqmxE -trseqmxE. Qed.

End CStronglyDiscreteTheory.

Section CBezoutCStronglyDiscrete.

Variable R : bezoutRingType.
Variable CR : cbezoutRingType R.

Definition cbmember n (x : CR) (I : seqmatrix CR) :=
  match cdiv x (cprincipal_gen n I) with
    | Some a => Some (mulseqmx 1 1 (cprincipal_w1 n I) (scalar_seqmx 1 a))
    | None   => None
  end.

Lemma cbmemberE n x (I : 'rV[R]_n) :
  omap trans (bmember x I) = cbmember n (trans x) (trans I).
Proof.
rewrite /bmember /cbmember -cprincipal_genE -cdivE.
case: odivrP => //= a ha.
by rewrite -cprincipal_w1E scalar_seqmxE /trans /= -mulseqmxE.
Qed.

Definition cbezout_cstronglyDiscreteMixin := CStronglyDiscrete.Mixin cbmemberE.
Canonical Structure cbezout_cstronglyDiscreteType :=
  Eval hnf in CStronglyDiscreteType R cbezout_cstronglyDiscreteMixin.

End CBezoutCStronglyDiscrete.