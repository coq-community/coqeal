Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice matrix bigop zmodp mxalgebra poly.

Require Import cssralg dvdring cdvdring seqmatrix.
Require Import coherent stronglydiscrete cstronglydiscrete ccoherent.
Require Import prufer cprufer.
Require Import Zinfra Coq.ZArith.Zdiv Coq.ZArith.Zabs.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** Z computations *)
Section Z.

Time Eval vm_compute in (clcm 2%Z 3%Z).
Time Eval vm_compute in (cbcap 1 2 [::[::2%Z]] [::[::3%Z;6%Z]]).

Let T := [stronglyDiscreteType of [bezoutRingType of Z]].
Let T' := [coherentRingType of [bezoutRingType of Z]].
Definition Z_CSMixin :=
  @CStronglyDiscreteMixin T [cringType Z of Z] (@cbmember _ _) (@cbmemberE _ _).
Canonical Structure Z_cstronglyDiscreteType :=
  Eval hnf in CStronglyDiscreteType T Z_CSMixin.

Eval vm_compute in (cmember 1%N 6%Z [::[:: 2%Z]]).

Definition Z_ccoherentMixin :=
  @CCoherentRing.Mixin T' Z_cstronglyDiscreteType _ _
                       (@cbsolve_row_intE _ _) (@cbsize_solve_intE _ _).
Canonical Structure Z_ccoherentType :=
  Eval hnf in CCoherentRingType T Z_ccoherentMixin.

Time Eval vm_compute in (csolve_row 2 [::[::2%Z;3%Z]]).
Time Eval vm_compute in (csolve_row 1 [::[::2%Z]]).
Time Eval vm_compute in (csolveMxN 2 2 [::[:: 1%Z;2%Z];[::2%Z;4%Z]]).
Time Eval vm_compute in (csolveGeneral 1 1 [::[:: 2%Z]] [::[::1%Z]]).
Time Eval vm_compute in (csolveGeneral 1 2 [::[:: 2%Z; 3%Z]] [::[::4%Z]]).
Time Eval vm_compute in (csolveGeneral 2 2 [::[:: 2%Z; 3%Z];[:: 4%Z; 6%Z]] [::[::4%Z];[:: 8%Z]]).
Time Eval vm_compute in (csolveGeneral 2 2 (trseqmx [::[:: 0%Z; 2%Z];[:: 1%Z; 0%Z]]) [::[::2%Z];[:: 0%Z]]).

(* Open Scope Z_scope. *)

(* Eval vm_compute in csolveGeneral 2 2 (trseqmx [::[:: 0; 2];[:: 1; 0]]) [::[::2];[:: 0]] . *)


Let T'' := [pruferDomainType of [bezoutRingType of Z]].
Definition Z_cpruferMixin :=
  @CPruferDomainMixin T'' [cdvdRingType Z of Z] _ (@cbezout_calcE _ _).
Canonical Structure Z_cpruferType :=
  Eval hnf in CPruferDomainType T Z_cpruferMixin.
Check cinv_id.

Eval vm_compute in (cprufer 2%Z 3%Z).
Eval vm_compute in (cplm 2%N [::[:: 2%Z; 3%Z]]).
Eval vm_compute in (cplm 3 [::[:: 2%Z; 3%Z; 5%Z]]).
Eval vm_compute in (cpmember 1%N 4%Z [::[:: 2%Z]]).
Eval vm_compute in (cpcapc 1 1 [:: [:: 2%Z]] [:: [:: 3%Z]]).
Eval vm_compute in (cinv_id 2 0 [:: [:: 2%Z; 3%Z]]).
Eval vm_compute in (cmulidc 2 2 [:: [:: 2%Z; 3%Z]] [:: [:: (-2)%Z; 2%Z]]).
Eval vm_compute in (cprincipal 4 [:: [:: (-4)%Z; 4%Z; (-6)%Z; 6%Z]]).

End Z.