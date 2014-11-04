Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice matrix bigop zmodp mxalgebra poly.

Require Import cssralg dvdring cdvdring seqmatrix.
Require Import coherent stronglydiscrete cstronglydiscrete.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** "Computable" Coherent rings *)
Module CCoherentRing.

Record mixin_of (R : coherentRingType) (CR : cstronglyDiscreteType R) : Type
 := Mixin {
  csize_solve : nat -> seqmatrix CR -> nat;
  csolve_row : nat -> seqmatrix CR -> seqmatrix CR;
  _ : forall n (V : 'rV[R]_n),
       seqmx_of_mx CR (solve_row V) = csolve_row n (seqmx_of_mx _ V);
  _ : forall n (V: 'rV[R]_n), size_solve V = csize_solve n (seqmx_of_mx _ V)
}.

Section ClassDef.

Variable R : coherentRingType.
Implicit Type phR : phant R.

Structure class_of (V : Type) := Class {
  base  : CStronglyDiscrete.class_of R V;
  mixin : mixin_of (CStronglyDiscrete.Pack _ base V)
}.

Local Coercion base : class_of >-> CStronglyDiscrete.class_of.

Structure type phR : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):= let: Pack _ c _ := cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.
Definition pack phR T V0 (m0 : mixin_of (@CStronglyDiscrete.Pack R _ T V0 T)) :=
  fun bT b & phant_id (@CStronglyDiscrete.class _ phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.
Definition cringType phR cT := CRing.Pack phR (@class phR cT) cT.
Definition cstronglyDiscreteType phR cT := CStronglyDiscrete.Pack phR (@class phR cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CStronglyDiscrete.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.
Coercion cringType: type >-> CRing.type.
Canonical Structure cringType.
Coercion cstronglyDiscreteType: type >-> CStronglyDiscrete.type.
Canonical Structure cstronglyDiscreteType.

Notation ccoherentRingType R := (@type _ (Phant R)).
Notation CCoherentRingType R m := (@pack _ (Phant R) _ _ m _ _ id _ id).
Notation CCoherentRingMixin := Mixin.
Notation "[ 'ccoherentRingType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'ccoherentRingType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'ccoherentRingType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'ccoherentRingType' T 'of'  V ]") : form_scope.
End Exports.

End CCoherentRing.

Export CCoherentRing.Exports.

Definition csize_solve (R : coherentRingType) (CR : ccoherentRingType R) :=
  CCoherentRing.csize_solve (CCoherentRing.class CR).
Definition csolve_row (R : coherentRingType) (CR : ccoherentRingType R) :=
  CCoherentRing.csolve_row (CCoherentRing.class CR).

Section CCoherentRingTheory.

Variable R : coherentRingType.
Variable CR : ccoherentRingType R.

Lemma csize_solveE : forall n (V : 'rV[R]_n),
  size_solve V = csize_solve n (seqmx_of_mx CR V).
Proof. by case: CR => [? [? []]]. Qed.

Lemma csolve_rowE : forall n (V : 'rV[R]_n),
  seqmx_of_mx CR (solve_row V) = csolve_row n (seqmx_of_mx _ V).
Proof. by case: CR => [? [? []]]. Qed.

Fixpoint csize_solveMxN  m n (M : seqmatrix CR) {struct m} : nat :=
  match m with
    | S p =>
      let: u := usubseqmx 1 M in
      let: k := csize_solve n u in
       csize_solveMxN p k (mulseqmx n k (dsubseqmx 1 M) (csolve_row n u))
    | _ => n
end.

Lemma csize_solveMxNE : forall m n (M: 'M[R]_(m,n)),
  size_solveMxN M = csize_solveMxN m n (seqmx_of_mx CR M).
Proof.
elim => [ | p hi] n; first by move => M; rewrite flatmx0 /=.
rewrite [p.+1]/(1 + p)%N => M /=.
by rewrite dsubseqmxE usubseqmxE -csolve_rowE -csize_solveE mulseqmxE hi.
Qed.

Fixpoint csolveMxN (m n : nat) (M : seqmatrix CR) : seqmatrix CR :=
  match m with
    | S p => (* M : p+1, n *)
      let u := usubseqmx 1 M in  (* 1, n *)
      let d := dsubseqmx 1 M in  (* p , n *)
      let G := csolve_row n u in  (* n, size_solve u *)
      let k := csize_solve n u in
      let R := mulseqmx n k d G in  (* p , size_solve u *)
        mulseqmx k (csize_solveMxN p k R) G (csolveMxN p k R)
    | _ => seqmx1 CR n
  end.

Lemma csolveMxNE : forall m n (M : 'M[R]_(m,n)),
  seqmx_of_mx _ (solveMxN M) = csolveMxN m n (seqmx_of_mx _ M).
Proof.
elim => [ M | m hi] n; first by rewrite flatmx0 /= seqmx1E.
rewrite [m.+1]/(1 + m)%N => M /=.
rewrite !usubseqmxE !dsubseqmxE -!csolve_rowE -!csize_solveE.
by rewrite mulseqmxE -hi -csize_solveMxNE mulseqmxE.
Qed.

Fixpoint csolveGeneral (m n : nat) (M : seqmatrix CR) (A : seqmatrix CR) :
 option (seqmatrix CR) :=
 match m with
 | S p =>
  let G1 := csolve_row n (usubseqmx 1 M) in
  let X1 := cmember n (A O O) (usubseqmx 1 M) in
   obind (fun x1 =>
    obind (fun xn =>
        Some (addseqmx x1 (mulseqmx (csize_solve n (usubseqmx 1 M)) 1 G1 xn)))
    (csolveGeneral p (csize_solve n (usubseqmx 1 M))
        (mulseqmx n (csize_solve n (usubseqmx 1 M)) (dsubseqmx 1 M) G1)
        (subseqmx (dsubseqmx 1 A) (mulseqmx n 1 (dsubseqmx 1 M) x1)))
      ) X1
    | _ => Some (seqmx0 CR n 1)
end.

Lemma csolveGeneralE : forall m n (M : 'M[R]_(m,n)) (A : 'cV[R]_m),
  omap (@seqmx_of_mx _ CR n 1) (solveGeneral M A) =
   csolveGeneral m n (seqmx_of_mx CR M) (seqmx_of_mx CR A).
Proof.
elim => [m M A|m ih n]; first by rewrite /= seqmx0E.
rewrite [m.+1]/(1 + m)%N => M A /=.
rewrite !usubseqmxE !dsubseqmxE (seqmxE _ _ 0 0) -csolve_rowE -csize_solveE.
rewrite mulseqmxE -cmemberE.
case: member_specP => //= I _.
rewrite mulseqmxE -subseqmxE -ih.
case: solveGeneralP => //= X _.
by rewrite mulseqmxE addseqmxE.
Qed.

End CCoherentRingTheory.

(** Proof that computable bezout domains are computable coherent *)
Section CBezoutCoherent.

Variable R : bezoutRingType.
Variable CR : cbezoutRingType R.

Definition cbcap_size (I J : seqmatrix CR) := 0%N.

Lemma cbcap_sizeE : forall (m n : nat) (I : 'rV_m) (J : 'rV[R]_n),
  bcap_size I J = cbcap_size (seqmx_of_mx CR I) (seqmx_of_mx CR J).
Proof. by []. Qed.

Definition cbcap m n (I : seqmatrix CR) (J : seqmatrix CR) :=
  scalar_seqmx 1 (clcm (cprincipal_gen m I) (cprincipal_gen n J)).

Lemma cbcapE m n (I : 'rV_m) (J : 'rV[R]_n) :
  seqmx_of_mx CR (bcap I J) = cbcap m n (trans I) (trans J).
Proof. by rewrite /bcap /cbcap -!cprincipal_genE -clcmE scalar_seqmxE. Qed.

(* (* Not necessary with subidW *)
Definition cbcap_wl m n (I : seqmatrix CR) (J : seqmatrix CR) :=
  let a := cprincipal_gen m I in
  let b := cprincipal_gen n J in
  mulseqmx 1 1 (cprincipal_w1 m I) (scalar_seqmx 1 (odflt (zero CR) (cdiv b (cgcd a b)))).

Lemma cbcap_wlE m n (I : 'rV_m) (J : 'rV_n) :
  trans (bcap_wl I J) = cbcap_wl m n (trans I) (trans J).
Proof.
rewrite /bcap_wl /cbcap_wl -!cprincipal_genE -cgcdE -cdivE -cprincipal_w1E.
rewrite {1}/trans /= -mulseqmxE -scalar_seqmxE.
by case: odivrP=> //=; rewrite zeroE.
Qed.

Definition cbcap_wr m n (I : seqmatrix CR) (J : seqmatrix CR) :=
  let a := cprincipal_gen m I in
  let b := cprincipal_gen n J in
  mulseqmx 1 1 (cprincipal_w1 n J) (scalar_seqmx 1 (odflt (zero CR) (cdiv a (cgcd a b)))).

Lemma cbcap_wrE m n (I : 'rV_m) (J : 'rV_n) :
  trans (bcap_wr I J) = cbcap_wr m n (trans I) (trans J).
Proof.
rewrite /bcap_wr /cbcap_wr -!cprincipal_genE -cgcdE -cdivE -cprincipal_w1E.
rewrite {1}/trans /= -mulseqmxE -scalar_seqmxE.
by case: odivrP=> //=; rewrite zeroE.
Qed.
*)

Definition cbcap_wl m n (I : seqmatrix CR) (J : seqmatrix CR) :=
  csubidW m 1 (cbcap m n I J) I.
Definition cbcap_wr m n (I : seqmatrix CR) (J : seqmatrix CR) :=
  csubidW 1 n (cbcap m n I J) J.

Fixpoint cbsize_solve_int (n : nat) (I : seqmatrix CR) := match n with
  | 0   => 0%N
  | S p => let v  := lsubseqmx 1 I in
           let vs := rsubseqmx 1 I in
           ((cbcap_size v (oppseqmx vs)).+1 + cbsize_solve_int p vs)%N
end.

Lemma cbsize_solve_intE : forall (n : nat) (I : 'rV[R]_n),
  size_solve I = cbsize_solve_int n (seqmx_of_mx CR I).
Proof.
rewrite /size_solve; elim => [|n ih]; first by move=> I; rewrite thinmx0.
rewrite [n.+1]/(1 + n)%N=> I /=.
by rewrite rsubseqmxE lsubseqmxE -oppseqmxE -cbcap_sizeE /bcap_size /= -ih.
Qed.

Fixpoint cbsolve_row_int (n : nat) (I : seqmatrix CR) : seqmatrix CR :=
  match n with
    | 0 => seqmx0 _ n n
    | S p => let v  := lsubseqmx 1 I in
             let vs := rsubseqmx 1 I in
             let m0 := cbsolve_row_int p vs in
             let wv := cbcap_wl 1 p v (oppseqmx vs) in
             let wvs := cbcap_wr 1 p v (oppseqmx vs) in
             block_seqmx (if v == seqmx0 CR 1 1 then @delta_seqmx _ CR 1 1 0 0
                                                else wv)
                         (seqmx0 CR 1 (cbsize_solve_int p vs))
                         (if v == seqmx0 CR 1 1 then seqmx0 CR p 1 else wvs)
                         m0
  end.

Lemma cbsolve_row_intE : forall (n : nat) (I : 'rV[R]_n),
  seqmx_of_mx CR (solve_row I) = cbsolve_row_int n (trans I).
Proof.
rewrite /solve_row; elim => [I|n ih]; first by rewrite thinmx0 seqmx0E.
rewrite [n.+1]/(1 + n)%N=> I /=.
rewrite !rsubseqmxE !lsubseqmxE -oppseqmxE -ih delta_seqmxE -!cbsize_solve_intE.
rewrite /cap_wl /cap_wr /cbcap_wl /cbcap_wr seqmx_of_mx_eq0.
by case: ifP=> h;
   rewrite -(@block_seqmxE _ _ 1 _ 1) !seqmx0E // !csubidWE -cbcapE.
Qed.

End CBezoutCoherent.