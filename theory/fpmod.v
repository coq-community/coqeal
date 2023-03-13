(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
From mathcomp Require Import ssralg fintype perm choice matrix bigop zmodp mxalgebra poly.

Require Import ssrcomplements stronglydiscrete coherent edr.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope mxpresentation_scope.

Reserved Notation "{ 'fpmod' T }" (at level 0, format "{ 'fpmod' T }").
Reserved Notation "''Mor' ( M , N )" (at level 8, format "''Mor' ( M ,  N )").
Reserved Notation "''Mono' ( M , N )" (at level 8, format "''Mono' ( M ,  N )").
Reserved Notation "''Epi' ( M , N )" (at level 8, format "''Epi' ( M ,  N )").
Reserved Notation "''Iso' ( M , N )" (at level 8, format "''Iso' ( M ,  N )").
Reserved Notation "''End' ( M )" (at level 8, format "''End' ( M )").
Reserved Notation "''Aut' ( M )" (at level 8, format "''Aut' ( M )").
Reserved Notation "M %= N" (at level 70, no associativity).
Reserved Notation "A ** B" (at level 40, left associativity, format "A  **  B").
Reserved Notation "x ^^-1" (at level 3, left associativity, format "x ^^-1").

Section morphismDef.

Variable R : coherentRingType.

(** Module *)
Record fpmod := FPmod {
  nbrel : nat;
  nbgen : nat;
  pres  : 'M[R]_(nbrel, nbgen)
}.

Definition fpmod_of of phant R := fpmod.
(* Identity Coercion type_fpmod_of : fpmod_of >-> fpmod. *) (* Is this necessary? *)

(* We want morphism_of_rect so temporarily add this: *)
Set Nonrecursive Elimination Schemes.

(** Morphisms *)
Record morphism_of (M N : fpmod) :=
  Morphism { matrix_of_morphism : 'M[R]_(nbgen M,nbgen N);
             _ : (pres N %| pres M *m matrix_of_morphism)%MP }.

Unset Nonrecursive Elimination Schemes.

End morphismDef.

Notation "{ 'fpmod' T }" := (fpmod_of (Phant T)).
Coercion matrix_of_morphism : morphism_of >-> matrix.
Notation "M %:m" := (M : 'M__) (at level 2, format "M %:m").
Notation "''Mor' ( M , N )" := (morphism_of M N) : type_scope.
Notation "M %:mor" := (M : 'Mor(_,_)) (at level 2, format "M %:mor").
Notation "''End' ( M )" := (morphism_of M M) : type_scope.

Definition source (R : coherentRingType) (M N : {fpmod R}) (phi : 'Mor(M, N)) := M.
Definition target (R : coherentRingType) (M N : {fpmod R}) (phi : 'Mor(M, N)) := N.

Section morphismTheory.

Variable R : coherentRingType.
Local Open Scope mxpresentation_scope.

Section equality.
Variables (M N : {fpmod R}).
Definition eqmor (phi psi : 'Mor(M,N)) := pres N %| phi%:m - psi%:m.

Lemma eqmor_refl : reflexive eqmor.
Proof. by move=> phi; rewrite /eqmor subrr. Qed.
Hint Resolve eqmor_refl : core.

Lemma eqmorxx x : eqmor x x. Proof. exact. Qed.

Lemma eqmor_sym : symmetric eqmor.
Proof. by move=> phi1 phi2; rewrite /eqmor -dvdmxN opprB. Qed.
Hint Resolve eqmor_sym : core.

Lemma eqmor_trans : transitive eqmor.
Proof.
rewrite /eqmor => phi2 phi1 phi3 phi12 phi23.
by rewrite -[phi1%:m](addrNK phi2%:m) -addrA dvdmxD.
Qed.
Hint Resolve eqmor_trans : core.

Lemma eqmor_ltrans : left_transitive eqmor.
Proof. exact: sym_left_transitive. Qed.

Lemma eqmor_rtrans : right_transitive eqmor.
Proof. exact: sym_right_transitive. Qed.

End equality.

Section general.

Variables (M N K : {fpmod R}).

(* reexporting dvdmx_morphism *)
Lemma dvdmx_morphism (phi : 'Mor(M, N)) : (pres N %| pres M *m phi).
Proof. by case: phi. Qed.

(* Constructor for 1 morphism *)
Lemma morphism1_subproof x (X : 'M_(x, _)) : X %| pres N -> X %| pres N *m 1%:M.
Proof. by rewrite mulmx1. Qed.

Definition Morphism1 x (X : 'M_(x, nbgen N)) (dvdXN : X %| pres N) : 'Mor(N, FPmod X) :=
  @Morphism _ _ (FPmod X) _ (@morphism1_subproof x X dvdXN).

Variables (n : nat) (X : 'M[R]_(n, nbgen M)).

Definition source_of_mx := FPmod ((pres M).-ker X).

Lemma mor_of_mx_proof : pres M %| pres source_of_mx *m X.
Proof. by rewrite -dvd_ker. Qed.

Definition mor_of_mx := Morphism mor_of_mx_proof.

End general.

Section zmodType.

Variables (M N : {fpmod R}).

Canonical morphism_subType := Eval hnf in
  [subType for (@matrix_of_morphism _ _ _) by (@morphism_of_rect _ M N)].
Definition morphism_eqMixin := [eqMixin of 'Mor(M, N) by <:].
Canonical morphism_eqType := EqType 'Mor(M, N) morphism_eqMixin.
Definition morphism_choiceMixin := [choiceMixin of 'Mor(M, N) by <:].
Canonical morphism_choiceType := ChoiceType 'Mor(M, N) morphism_choiceMixin.

Implicit Types (phi : 'Mor(M, N)).

(** Zero *)
(* The zero morphism between two object *)
Fact zeromor_proof : pres N %| pres M *m 0.
Proof. by rewrite mulmx0 dvdmx0. Qed.

Definition zeromor : 'Mor(M,N) := Morphism zeromor_proof.

(** Addition *)
Fact addmor_proof phi1 phi2 :
  pres N %| pres M *m (phi1%:m + phi2%:m).
Proof. by rewrite mulmxDr dvdmxD // dvdmx_morphism. Qed.

Definition addmor phi1 phi2 : 'Mor(M, N) :=
  Morphism (addmor_proof phi1 phi2).

(** Subtraction *)
Fact oppmor_proof phi : pres N %| pres M *m (- phi%:m).
Proof. by rewrite mulmxN dvdmxN dvdmx_morphism. Qed.

Definition oppmor phi : 'Mor(M, N) := Morphism (oppmor_proof phi).

Fact addmA_subproof : associative addmor.
Proof. by move=> x y z; apply: val_inj; apply: addrA. Qed.
Fact addmC_subproof : commutative addmor.
Proof. by move=> x y; apply: val_inj; apply: addrC. Qed.
Fact add0m_subproof : left_id zeromor addmor.
Proof. by move=> x; apply: val_inj; apply: add0r. Qed.
Fact addNm_subproof : left_inverse zeromor oppmor addmor.
Proof. by move=> x; apply: val_inj; apply: addNr. Qed.

Definition morphism_zmodMixin :=
  ZmodMixin addmA_subproof addmC_subproof add0m_subproof addNm_subproof.
Canonical morphism_zmodType := ZmodType 'Mor(M, N) morphism_zmodMixin.

End zmodType.

Section category.

Section defs.

Variables (M N K : {fpmod R}).

(** Identity endomorphism *)
Definition idm : 'End(M) := Morphism (morphism1_subproof (dvdmx_refl _)).
Implicit Types (phi : 'Mor(M, N)) (psi : 'Mor(N, K)).

(** Composition *)
Fact mulmor_proof phi psi : pres K %| pres M *m (phi *m psi).
Proof.
rewrite mulmxA (dvdmx_trans (dvdmx_morphism psi)) //.
by rewrite dvdmxMr // dvdmx_morphism.
Qed.

Definition mulmor phi psi : 'Mor(M, K) := Morphism (mulmor_proof phi psi).

End defs.
Arguments idm {_}.
Infix "**" := mulmor : mxpresentation_scope.
Infix "%=" := eqmor : mxpresentation_scope.

Section theory.
Variables (M N P Q : {fpmod R}).

Lemma mul1mor (phi : 'Mor(M,P)) : idm ** phi = phi.
Proof. by apply: val_inj; rewrite /= mul1mx. Qed.

Lemma mulmor1 (phi : 'Mor(M,P)) : phi ** idm = phi.
Proof. by apply: val_inj; rewrite /= mulmx1. Qed.

Lemma mul0mor (phi : 'Mor(M,P)) : 0 ** phi = 0 :> 'Mor(N,P).
Proof. by apply: val_inj; rewrite /= mul0mx. Qed.

Lemma mulmor0 (phi : 'Mor(M,P)) : phi ** 0 = 0 :> 'Mor(M, Q).
Proof. by apply: val_inj; rewrite /= mulmx0. Qed.

Lemma mulmorA (psi : 'Mor(M,N)) (phi : 'Mor(N,P)) (kapa : 'Mor(P,Q)) :
  psi ** (phi ** kapa) = (psi ** phi) ** kapa.
Proof. by apply: val_inj; rewrite /= mulmxA. Qed.

Lemma mulmorDl (phi1 phi2 : 'Mor(M, N)) (psi : 'Mor(N, P)) :
  (phi1 + phi2) ** psi = phi1 ** psi + phi2 ** psi.
Proof. by apply: val_inj => /=; rewrite mulmxDl. Qed.

Lemma mulmorDr (psi : 'Mor(M, N)) (phi1 phi2 : 'Mor(N, P)) :
  psi ** (phi1 + phi2)= psi ** phi1 + psi ** phi2.
Proof. by apply: val_inj => /=; rewrite mulmxDr. Qed.

Lemma mulmorN (phi : 'Mor(M, N)) (psi : 'Mor(N, P)) :
  phi ** (- psi) = - (phi ** psi).
Proof. by apply: val_inj => /=; rewrite mulmxN. Qed.

Lemma mulNmor (phi : 'Mor(M, N)) (psi : 'Mor(N, P)) :
  (- phi) ** psi = - (phi ** psi).
Proof. by apply: val_inj => /=; rewrite mulNmx. Qed.

Lemma mulmorBl (phi1 phi2 : 'Mor(M, N)) (psi : 'Mor(N, P)) :
  (phi1 - phi2) ** psi = phi1 ** psi - phi2 ** psi.
Proof. by rewrite mulmorDl mulNmor. Qed.

Lemma mulmorBr (psi : 'Mor(M, N)) (phi1 phi2 : 'Mor(N, P)) :
  psi ** (phi1 - phi2) = psi ** phi1 - psi ** phi2.
Proof. by rewrite mulmorDr mulmorN. Qed.

Lemma eqmorMl (psi : 'Mor(M, N)) (phi1 phi2 : 'Mor(N, P)) :
  phi1 %= phi2 -> psi ** phi1 %= psi ** phi2.
Proof. by move=> phi12; rewrite /eqmor -mulmxBr dvdmxMl. Qed.

Lemma eqmorMr (psi : 'Mor(N, P)) (phi1 phi2 : 'Mor(M, N)) :
  phi1 %= phi2 -> phi1 ** psi %= phi2 ** psi.
Proof.
rewrite /eqmor=> phi12.
by rewrite -mulmxBl (dvdmx_trans (dvdmx_morphism psi)) ?dvdmxMr.
Qed.

End theory.
End category.

End morphismTheory.
Arguments idm {_ _}.
Infix "**" := mulmor.
Infix "%=" := eqmor.
#[export] Hint Resolve eqmorxx : core.

Section KernelAndCo.
Variable R : coherentRingType.
Variables (M N : {fpmod R}) (phi : 'Mor(M,N)).

(** Kernel

The kernel is the submodule defined by the monomorphism induced by N.-ker:

       pres kermod
     R ---------> "kermod"
     |            |
     |            | kernel := N.-ker phi
     v     M      v
     R ---------> R
     |            |
     |            | phi
     v     N      v
     R ---------> R

*)
Definition kermod := source_of_mx (((pres N).-ker) phi).
Definition kernel : 'Mor(kermod,_) := mor_of_mx ((pres N).-ker phi).
Definition injm := kernel %= 0.

(** Quotienting is just matrix stacking *)
Definition quot_by : {fpmod R} := FPmod (col_mx (pres N) phi).

Lemma dvd_quot_mx x (X : 'M_(x, _)) : pres N %| X -> pres quot_by %| X.
Proof. by move=> dvdNX; apply/dvd_col_mxP; exists 0; rewrite mul0mx subr0. Qed.

(** Cokernel
We have a commutative diagram:

          M
     R--------> R
     |          |
     |          | phi
     v    N     v
     R--------> R
     |          |
     |  ( N )   | 1
     v  (phi)   v
     R--------->R

The cokernel morphism is the 1 morphism of N onto pcoker *)
Definition coker : 'Mor(N, quot_by) := Morphism1 (dvd_quot_mx (dvdmx_refl _)).
Definition surjm := coker %= 0.
Definition isom := injm && surjm.

Lemma mulkmor : kernel ** phi %= 0.
Proof. by rewrite /eqmor subr0 ker_modK. Qed.

Lemma mulmorc : phi ** coker %= 0.
Proof. by rewrite /eqmor subr0 /= mulmx1 dvd_col_mxl. Qed.

End KernelAndCo.

(* Warning: kernel and coker are not compatible with %=, if we
   quotiented 'Mor by %=, we should always pick the kernel/coker wrt
   the canonical representative of the equivalence class *)

Section morphismProperties.

Variable R : coherentRingType.
Variables (M N : {fpmod R}) (phi : 'Mor(M, N)).

Definition is_mono :=
  forall (P : {fpmod R}) (psi : 'Mor(P, M)), psi ** phi %= 0 -> psi %= 0.

Definition is_epi  :=
  forall (P : {fpmod R}) (psi : 'Mor(N, P)), phi ** psi %= 0 -> psi %= 0.

(* A morphism is an isomorphism if it is both injective and surjective *)
Lemma monoP : reflect is_mono (kernel phi %= 0).
Proof.
apply: (iffP idP); last by apply; rewrite mulkmor.
rewrite /is_mono /eqmor subr0 => /= dvdMK P psi.
rewrite subr0 => dvd_phi_psi.
by rewrite (dvdmx_trans dvdMK) //= subr0 dvd_ker.
Qed.

Lemma epiP : reflect is_epi (coker phi %= 0).
Proof.
apply: (iffP idP); last by apply; rewrite mulmorc.
rewrite /is_epi /eqmor subr0.
(* should be shortened *)
move=> /dvd_col_mxP [X /dvdmxP [Z Z_def]] P psi.
rewrite !subr0 => /= /dvdmxP [Y] /(congr1 (mulmx X)).
rewrite !mulmxA -[X *m phi](addrNK 1%:M) mulmxDl mul1mx.
move/(canRL (addKr _)) ->.
rewrite -mulNmx opprB Z_def -mulmxA dvdmxD //; last first.
  by rewrite mulmxA dvdmxMl.
by rewrite -mulmxA dvdmxMl // dvdmx_morphism.
Qed.

Lemma rinv_inj (psi : 'Mor(N, M)) :
  phi ** psi %= idm -> kernel phi %= 0.
Proof.
move/(eqmorMl (kernel phi)); rewrite mulmorA mulmor1.
by rewrite (eqmor_ltrans (eqmorMr _ (mulkmor _))) mul0mor eqmor_sym.
Qed.

Lemma linv_surj (psi : 'Mor(N, M)) :
   psi ** phi %= idm -> coker phi %= 0.
Proof.
move/(eqmorMr (coker phi)); rewrite -mulmorA mul1mor.
by rewrite (eqmor_ltrans (eqmorMl _ (mulmorc _))) mulmor0 eqmor_sym.
Qed.

Definition isomorphisms (psi : 'Mor(N, M)) :=
    (phi ** psi %= idm) && (psi ** phi %= idm).

Lemma isoP : reflect (exists psi, isomorphisms psi) (isom phi).
Proof.
rewrite /isom /injm /surjm; apply: (iffP andP) => [[]|[psi]]; last first.
  by move=> /andP [/rinv_inj -> /linv_surj ->].
rewrite /eqmor !subr0.
move=> phi_inj /dvd_col_mxP /sig_eqW [X /= hX].
have Xmor : pres M %| pres N *m X.
  rewrite (dvdmx_trans phi_inj) // dvd_ker -mulmxA -[X *m _](subrK 1%:M).
  by rewrite mulmxDr dvdmxDl ?mulmx1 ?dvdmxMl // -dvdmxN opprB.
exists (Morphism Xmor); rewrite /isomorphisms andbC /eqmor -dvdmxN opprB hX.
rewrite /eqmor (dvdmx_trans phi_inj) // dvd_ker mulmxBl mul1mx.
by rewrite -mulmxA -[X in _ - X]mulmx1 -mulmxBr dvdmxMl // -dvdmxN opprB.
Qed.

End morphismProperties.

Section MonoEpi.

Variable R : coherentRingType.
Variables (M N : {fpmod R}).

Record monomorphism_of := Monomorphism  {
  morphism_of_mono :> 'Mor(M, N);
                 _ : injm morphism_of_mono
}.

Record epimorphism_of := Epimorphism {
  morphism_of_epi :> 'Mor(M, N);
                _ : surjm morphism_of_epi
}.

Record isomorphism_of := Isomorphism {
  morphism_of_iso :> 'Mor(M, N);
                _ : isom morphism_of_iso
}.

Fact split_andb (a b : bool) : a -> b -> a && b.
Proof. by move=> pa pb; apply/andP. Qed.

Definition mono_of phi (phi_mono : is_mono phi) :=
  @Monomorphism phi (@introTF _ _ true (monoP phi) phi_mono).

Definition epi_of phi (phi_epi : is_epi phi) :=
  @Epimorphism phi (@introTF _ _ true (epiP phi) phi_epi).

Definition iso_of_kc phi (k : kernel phi %= 0) (c : coker phi %= 0) :
  isomorphism_of := @Isomorphism phi (split_andb k c).

Definition iso_of_me phi (phi_mono : is_mono phi) (phi_epi : is_epi phi) :=
  @iso_of_kc phi (@introTF _ _ true (monoP phi) phi_mono)
                 (@introTF _ _ true (epiP phi) phi_epi).

Definition iso_of_isom phi psi (isom : @isomorphisms R M N phi psi) :=
  Isomorphism (@introTF _ _ true (isoP phi) (ex_intro _ psi isom)).

(** Helper for morphism reconstruction, à la tuple.v *)
Definition monomorphism phi MkMono : monomorphism_of :=
  MkMono (let: Monomorphism _ phi_inj := phi
          return injm phi in phi_inj).
Definition epimorphism  phi MkEpi  : epimorphism_of :=
  MkEpi  (let: Epimorphism _ phi_epi := phi
          return surjm phi in phi_epi).
Definition isomorphism phi MkIso : isomorphism_of :=
  MkIso (let: Isomorphism _ phi_iso := phi
          return isom phi in phi_iso).

Lemma eqmor_epi (phi psi : 'Mor(M, N)) :
   phi %= psi -> is_epi phi -> is_epi psi.
Proof.
move=> eqp phi_epi P kapa.
by rewrite -(eqmor_ltrans (eqmorMr _ eqp)) => /phi_epi.
Qed.

Lemma eqmor_mono (phi psi : 'Mor(M, N)) :
   phi %= psi -> is_mono phi -> is_mono psi.
Proof.
move=> eqp phi_mono P kapa.
by rewrite -(eqmor_ltrans (eqmorMl _ eqp)) => /phi_mono.
Qed.

End MonoEpi.

Notation "''Mono' ( M , N )" := (monomorphism_of M N) : type_scope.
Notation "''Epi' ( M , N )"  := (epimorphism_of M N) : type_scope.
Notation "''Iso' ( M , N )"  := (isomorphism_of M N) : type_scope.
Notation "''Aut' ( M )" := (isomorphism_of M M) : type_scope.
Notation "[Mono 'of' phi ]" :=
  (monomorphism (fun phi_mono => @Monomorphism _ _ _ phi phi_mono))
    (at level 0, format "[Mono  'of'  phi ]").
Notation "[Epi 'of' phi ]" :=
  (epimorphism (fun phi_epi => @Epimorphism _ _ _ phi phi_epi))
    (at level 0, format "[Epi  'of'  phi ]").
Notation "[Iso 'of' phi ]" :=
  (isomorphism (fun phi_iso => @Isomorphism _ _ _ phi phi_iso))
    (at level 0, format "[Iso  'of'  phi ]").
Arguments eqmor_mono {R M N phi psi} _ _ _ _ _.
Arguments eqmor_epi {R M N phi psi} _ _ _ _ _.

Section MonoTheory.
Variable (R : coherentRingType).

Section Mono1.
Variables (M N : {fpmod R}).

Lemma kernel_eq0 (phi : 'Mono(M,N)) : kernel phi %= 0.
Proof. by case: phi. Qed.
Hint Resolve kernel_eq0 : core.

Lemma mono (phi : 'Mono(M,N)) : is_mono phi.
Proof. exact/monoP. Qed.
Hint Resolve mono : core.

Lemma mulmono_eq0 (L : {fpmod R}) (phi : 'Mono(M,N)) (Y : 'Mor(L, M)) :
  (Y ** phi %= 0) = (Y %= 0).
Proof.
apply/idP/idP; first by move/mono.
by move=> /eqmorMr /eqmor_ltrans ->; rewrite mul0mor.
Qed.

Variables (n : nat) (X : 'M[R]_(n, nbgen M)).

Fact mor_of_mx_inj : kernel (mor_of_mx X) %= 0.
Proof. by apply/monoP=> P psi; rewrite /= /eqmor !subr0 -dvd_ker. Qed.

Canonical mono_of_mx := Monomorphism mor_of_mx_inj.
End Mono1.

Lemma left_mono (M N L : {fpmod R}) (phi : 'Mor(M,N)) (psi : 'Mor(N,L)) :
  is_mono (phi ** psi) -> is_mono phi.
Proof.
by move=> mmono K kapa /(eqmorMr psi); rewrite mul0mor -mulmorA => /mmono.
Qed.

End MonoTheory.

#[export] Hint Resolve kernel_eq0 : core.
#[export] Hint Resolve mono : core.

Section EpiTheory.
Variable (R : coherentRingType).

Section Epi1.
Variables (M N : {fpmod R}).

Lemma coker_eq0 (phi : 'Epi(M,N)) : coker phi %= 0.
Proof. by case: phi. Qed.
Hint Resolve coker_eq0 : core.

Lemma epi (phi : 'Epi(M,N)) : is_epi phi.
Proof. exact/epiP. Qed.

Lemma mulepi_eq0 (L : {fpmod R}) (phi : 'Epi(M,N)) (Y : 'Mor(N, L)) :
  (phi ** Y %= 0) = (Y %= 0).
Proof.
apply/idP/idP; first by move/epi.
by move/eqmorMl/eqmor_ltrans ->; rewrite mulmor0.
Qed.
End Epi1.

Lemma right_epi (M N L : {fpmod R}) (phi : 'Mor(M,N)) (psi : 'Mor(N,L)) :
  is_epi (phi ** psi) -> is_epi psi.
Proof.
by move=> mepi K kapa /(eqmorMl phi); rewrite mulmor0 mulmorA => /mepi.
Qed.

End EpiTheory.

#[export] Hint Resolve coker_eq0 : core.
#[export] Hint Resolve epi : core.

Section IsoTheory.
Variable (R : coherentRingType) (M N : {fpmod R}).

Fact iso_kernel_eq0 (phi : 'Iso(M,N)) : kernel phi %= 0.
Proof. by case: phi => /= ? /andP[]. Qed.
Hint Resolve iso_kernel_eq0 : core.

Fact iso_coker_eq0 (phi : 'Iso(M,N)) : coker phi %= 0.
Proof. by case: phi => /= ? /andP[]. Qed.
Hint Resolve iso_coker_eq0 : core.

Canonical mono_of_iso phi := Monomorphism (iso_kernel_eq0 phi).
Canonical epi_of_iso phi := Epimorphism (iso_coker_eq0 phi).

Definition invmor (phi : 'Iso(M,N)) :=
  projT1 (sigW (isoP phi (split_andb (kernel_eq0 [Mono of phi])
                                        (coker_eq0 [Epi of phi])))).
Notation "phi ^^-1" := (invmor phi).

Lemma mulVmor (phi : 'Iso(M,N)) : phi^^-1 ** phi %= idm.
Proof. by rewrite /invmor; case: sigW => /= psi /andP []. Qed.

Lemma mulmorV (phi : 'Iso(M,N)) : phi ** phi^^-1 %= idm.
Proof. by rewrite /invmor; case: sigW => /= psi /andP []. Qed.

End IsoTheory.
Notation "phi ^^-1" := (invmor phi) : mxpresentation_scope.

Section theory.

Local Open Scope mxpresentation_scope.

Variable R : coherentRingType.

(* Kernel is mono *)
Fact kernelK (M N : {fpmod R}) (phi : 'Mor(M,N)) : kernel (kernel phi) %= 0.
Proof. by rewrite kernel_eq0. Qed.

Canonical mono_of_kernel (M N : {fpmod R}) (phi : 'Mor(M,N)) :=
  Monomorphism (kernelK phi).

(* cokernel is epi *)
Lemma cokerK (M N : {fpmod R}) (phi : 'Mor(M,N)) : coker (coker phi) %= 0.
Proof. by rewrite /eqmor subr0 dvd_col_mxl. Qed.

Canonical epi_of_coker (M N : {fpmod R}) (phi : 'Mor(M,N)) :=
  Epimorphism (cokerK phi).

(* The identity morphism is an isomorphism *)
Lemma isomorphisms_idm (M : {fpmod R}) : isomorphisms (@idm _ M) idm.
Proof. by apply/andP; split; rewrite mulmor1. Qed.

Lemma mulmor11 (M : {fpmod R}) : (@idm _ M) ** idm %= idm.
Proof. by rewrite mul1mor. Qed.

Canonical idm_iso (M : {fpmod R}) :=
  iso_of_kc (rinv_inj (mulmor11 M)) (linv_surj (mulmor11 M)).

(** Kernel universal property *)
Definition is_kernel (M N K : {fpmod R}) (phi : 'Mor(M,N))
  (k : 'Mor(K,M)) :=
  ((k ** phi %= 0) *
  forall L (psi : 'Mor(L,M)),
    reflect (exists Y, Y ** k %= psi) (psi ** phi %= 0))%type.

(** Our kernel construction has the universal property *)
Lemma kernelP (M N : {fpmod R}) (phi : 'Mor(M,N)) :
  is_kernel phi (kernel phi).
Proof.
split; first by rewrite mulkmor.
move=> L X; apply: (iffP idP) => [|[Y]]; last first.
  move/eqmorMr/eqmor_ltrans <-; rewrite -mulmorA.
  by rewrite (eqmor_ltrans (eqmorMl _ (mulkmor _))) mulmor0.
rewrite /eqmor; rewrite subr0 -dvd_ker => /dvdmxP [Y Yeq].
have Ymor : pres (source (kernel phi)) %| pres L *m Y.
  by rewrite /= dvd_ker -mulmxA -Yeq dvdmx_morphism.
by exists (Morphism Ymor); rewrite Yeq subrr.
Qed.

(** Any monomorphism is a kernel of its cokernel *)
Lemma mono_ker (M N : {fpmod R}) (phi : 'Mono(M,N)) :
  is_kernel (coker phi) phi.
Proof.
split; first by rewrite mulmorc.
move=> L X; apply: (iffP idP); last first.
  move=> [Y /eqmorMr /eqmor_ltrans <-]; rewrite -mulmorA.
  by rewrite (eqmor_ltrans (eqmorMl _ (mulmorc _))) mulmor0.
rewrite /eqmor subr0 /= mulmx1 => /dvd_col_mxP [Y Ydef].
suff Ymor : pres M %| pres L *m Y.
  by exists (Morphism Ymor); rewrite /= -dvdmxN opprB.
have := kernel_eq0 phi; rewrite /eqmor subr0 /=.
move=> /dvdmx_trans -> //; rewrite dvd_ker.
rewrite -mulmxA -[Y *m phi](addrNK X%:m) mulmxDr dvdmxD ?dvdmx_morphism //.
by rewrite dvdmxMl // -dvdmxN opprB.
Qed.

(* Quotienting by a morphism may allow you to factor it out *)
Lemma lift_subproof (M N L : {fpmod R})
  (phi : 'Mor(M,N)) (psi : 'Mor(N,L)) :
  phi ** psi %= 0 -> pres L %| pres (quot_by phi) *m psi.
Proof. by rewrite /eqmor subr0 /= mul_col_mx dvd_mx_col dvdmx_morphism. Qed.

(* Lifting a morphism psi wrt a quotient by phi *)
Definition lift (M N L : {fpmod R})
  (phi : 'Mor(M,N)) (psi : 'Mor(N,L)) : 'Mor(quot_by phi,L) :=
  if (phi ** psi %= 0) =P true is ReflectT P
  then Morphism (lift_subproof P) else 0.

(* We can factor a morphism psi by its lifting *)
Lemma mul_lift (M N L : {fpmod R}) (phi : 'Mor(M,N)) (psi : 'Mor(N,L)) :
  phi ** psi %= 0 -> coker phi ** lift phi psi %= psi.
Proof.
rewrite /lift; case: eqP => //= p _.
by rewrite /eqmor /= mul1mx subrr.
Qed.

(* The lifting of an epi is an epi *)
Lemma lift_epi (M N L : {fpmod R}) (phi : 'Mor(M,N)) (psi : 'Epi(N,L)) :
  phi ** psi %= 0 -> is_epi (lift phi psi).
Proof.
move=> /mul_lift psiP K kapa; rewrite eqmor_sym in psiP.
suff lepi : is_epi (lift phi psi) by move/lepi.
apply: right_epi (coker phi) _ _.
exact: (@eqmor_epi _ _ _ psi).
Qed.

Lemma mul_klift (M N : {fpmod R}) (psi : 'Mor(M,N)) :
  coker (kernel psi) ** lift (kernel psi) psi %= psi.
Proof. by rewrite mul_lift // mulkmor. Qed.

(* The lifting of phi to the quotient of its kernel is a monomorphism *)
Lemma lift_mono (M N : {fpmod R}) (psi : 'Mor(M,N)) :
  is_mono (lift (kernel psi) psi).
Proof.
apply/monoP; rewrite /eqmor subr0 /=.
rewrite (dvdmx_trans (dvd_col_mxl _ _)) // /lift.
by case: eqP (mulkmor psi).
Qed.

(** Universal property of the cokernel *)
Definition is_coker (M N C : {fpmod R}) (phi : 'Mor(M,N))
  (c : 'Mor(N,C)) :=
  ((phi ** c %= 0) *
  forall L (psi : 'Mor(N,L)),
    reflect (exists Y, c ** Y %= psi) (phi ** psi %= 0))%type.

(** Our coker construction satisfies the universal property of cokernels *)
Lemma cokerP (M N : {fpmod R}) (phi : 'Mor(M,N)) : is_coker phi (coker phi).
Proof.
split; first by rewrite mulmorc.
move=> L X; apply: (iffP idP) => [phiX|[Y]]; last first.
  move/eqmorMl/eqmor_ltrans <-; rewrite mulmorA.
  by rewrite (eqmor_ltrans (eqmorMr _ (mulmorc _))) mul0mor.
by exists (lift phi X); rewrite mul_lift.
Qed.

(* Factorisation lemma *)
Lemma factor_proof (M N P : {fpmod R}) (phi : 'Mono(N,P)) (psi : 'Mor(M,P)) :
  reflect (exists kapa, kapa ** phi %= psi) (psi ** coker phi %= 0).
Proof.
apply: (iffP idP) => [|[c]]; last first.
  move/eqmorMr/eqmor_ltrans <-; rewrite -mulmorA.
  by rewrite (eqmor_ltrans (eqmorMl _ (mulmorc _))) mulmor0.
rewrite /eqmor /= subr0 mulmx1 => /dvd_col_mxP [X Xdef].
suff Xmor : pres N %| pres M *m X.
  by exists (Morphism Xmor); rewrite -dvdmxN opprB.
have /monoP := @mono _ _ _ phi.
rewrite /eqmor /= subr0 => /dvdmx_trans -> //.
rewrite dvd_ker -mulmxA -[X *m _](addrNK psi%:m).
by rewrite mulmxDr dvdmxD ?dvdmx_morphism // dvdmxMl // -dvdmxN opprB.
Qed.

(* extraction of the factor *)
Definition factor (M N P : {fpmod R})
  (phi : 'Mor(N,P)) (psi : 'Mor(M,P)) : 'Mor(M,N) :=
  if (kernel phi %= 0) =P true is ReflectT phi_inj
  then if factor_proof (Monomorphism phi_inj) psi is ReflectT P
  then projT1 (sig_eqW P) else 0
  else 0.

(* property of the factor *)
Lemma factorP (M N P : {fpmod R}) (phi : 'Mono(N,P)) (psi : 'Mor(M,P)) :
  psi ** coker phi %= 0 -> factor phi psi ** phi %= psi.
Proof.
have := kernel_eq0 phi; rewrite /factor.
case: eqP => // phi_inj _; case: factor_proof => //= p _.
by case: sig_eqW.
Qed.

Notation "phi %/ psi" := (quot_by (factor phi psi)).

(** Every epimorphism is a cokernel of its kernel *)
Lemma epi_coker (M N : {fpmod R}) (phi : 'Epi(M,N)) :
  is_coker (kernel phi) phi.
Proof.
split; first by rewrite mulkmor.
move=> L psi; apply: (iffP idP); last first.
  move=> [Y /eqmorMl /eqmor_ltrans <-]; rewrite mulmorA.
  by rewrite (eqmor_ltrans (eqmorMr _ (mulkmor _))) mul0mor.
move/mul_lift; have /mul_lift := mulkmor phi.
set phi' := lift _ phi; set psi' := lift _ psi.
move=> phi'E psi'E.
have phi'_mono : is_mono phi' by apply: lift_mono.
have phi'_epi : is_epi phi' by apply: lift_epi; rewrite mulkmor.
set phi'' := @iso_of_me _ _ _ phi' phi'_mono phi'_epi.
exists (phi''^^-1 ** psi').
rewrite -(eqmor_ltrans (eqmorMr _ phi'E)) -(eqmor_rtrans psi'E).
rewrite -mulmorA eqmorMl // mulmorA.
by rewrite (eqmor_ltrans (eqmorMr _ (mulmorV phi''))) mul1mor.
Qed.

(** Introduction of direct sum, which play the role of the kernel *)
(* and the cokernel *)
Section dsum.
Variables (M N : {fpmod R}).

Definition dsum := FPmod (block_mx (pres M) 0 0 (pres N)).

Fact proj1_proof : pres M %| pres dsum *m (col_mx 1%:M 0).
Proof.
by rewrite mul_block_col !mulmx0 !addr0 mul0mx mulmx1 dvd_mx_col dvdmx0 andbT.
Qed.
Definition proj1 : 'Mor(dsum, M) := Morphism proj1_proof.

Lemma proj1_is_epi : is_epi proj1.
Proof.
move=> P phi; rewrite /eqmor !subr0 /=.
by rewrite mul_col_mx mul0mx mul1mx dvd_mx_col => /andP[].
Qed.
Canonical proj1_epi := epi_of proj1_is_epi.

Definition proj2_proof : pres N %| pres dsum *m (col_mx 0 1%:M).
Proof.
by rewrite mul_block_col !mulmx0 !add0r mul0mx mulmx1 dvd_mx_col dvdmx0 /=.
Qed.
Definition proj2 : 'Mor(dsum, N) := Morphism proj2_proof.

Lemma proj2_is_epi : is_epi proj2.
Proof.
move=> P phi; rewrite /eqmor !subr0 /=.
by rewrite mul_col_mx mul0mx mul1mx dvd_mx_col => /andP[].
Qed.
Canonical proj2_epi := epi_of proj2_is_epi.

Lemma inj1_proof : pres dsum %| pres M *m (row_mx 1%:M 0).
Proof.
apply/dvdmxP; exists (row_mx 1%:M 0).
by rewrite mul_mx_row mul_row_block !(mulmx0, mul0mx) !addr0 mul1mx mulmx1.
Qed.
Definition inj1 : 'Mor(M,dsum) := Morphism inj1_proof.

Lemma inj1_is_mono : is_mono inj1.
Proof.
move=> P phi; rewrite /eqmor !subr0 /= mul_mx_row mulmx1 mulmx0.
move=> /dvdmxP [X]; rewrite -[X]hsubmxK mul_row_block.
by rewrite !mulmx0 addr0 add0r => /eq_row_mx[-> _]; rewrite dvdmxMl.
Qed.
Canonical inj1_mono := mono_of inj1_is_mono.

Lemma inj2_proof : pres dsum %| pres N *m (row_mx 0 1%:M).
Proof.
apply/dvdmxP; exists (row_mx 0 1%:M).
by rewrite mul_mx_row mul_row_block !(mulmx0, mul0mx) !add0r mul1mx mulmx1.
Qed.
Definition inj2 : 'Mor(N,dsum) := Morphism inj2_proof.

Lemma inj2_is_mono : is_mono inj2.
Proof.
move=> P phi; rewrite /eqmor !subr0 /= mul_mx_row mulmx1 mulmx0.
move=> /dvdmxP [X]; rewrite -[X]hsubmxK mul_row_block.
by rewrite !mulmx0 addr0 add0r => /eq_row_mx[_ ->]; rewrite dvdmxMl.
Qed.
Canonical inj2_mono := mono_of inj2_is_mono.

Lemma inj1_proj2 : inj1 ** proj2 = 0.
Proof. by apply: val_inj; rewrite /= mul_row_col mulmx0 mul0mx addr0. Qed.

Lemma inj2_proj1 : inj2 ** proj1 = 0.
Proof. by apply: val_inj; rewrite /= mul_row_col mulmx0 mul0mx addr0. Qed.

Lemma inj1_proj1 : inj1 ** proj1 = idm.
Proof. by apply: val_inj; rewrite /= mul_row_col mulmx0 mul1mx addr0. Qed.

Lemma inj2_proj2 : inj2 ** proj2 = idm.
Proof. by apply: val_inj; rewrite /= mul_row_col mulmx0 mul1mx add0r. Qed.

Lemma dsum_is_product (P : {fpmod R}) (p1 : 'Mor(P,M)) (p2 : 'Mor(P,N)) :
  exists phi : 'Mor(P,dsum), p1 = phi ** proj1 /\ p2 = phi ** proj2.
Proof.
exists (p1 ** inj1 + p2 ** inj2).
rewrite !mulmorDl -!mulmorA inj1_proj1 inj1_proj2 inj2_proj1 inj2_proj2.
by rewrite !mulmor1 !mulmor0 addr0 add0r.
Qed.

Lemma dsum_is_coproduct (P : {fpmod R}) (i1 : 'Mor(M,P)) (i2 : 'Mor(N,P)) :
  exists phi : 'Mor(dsum,P), i1 = inj1 ** phi /\ i2 = inj2 ** phi.
Proof.
exists (proj1 ** i1 + proj2 ** i2).
rewrite !mulmorDr !mulmorA inj1_proj1 inj1_proj2 inj2_proj1 inj2_proj2.
by rewrite !mul1mor !mul0mor addr0 add0r.
Qed.

End dsum.

Section homology.

Variables (M N P : {fpmod R}).
Variables (phi : 'Mor(M, N)) (psi : 'Mor(N, P)).

Hypothesis mul_phi_psi : phi ** psi %= 0.

Definition homology := kernel psi %/ phi.

(* Alternative definition of homology used in singular and homalg: *)
(*      http://link.springer.com/chapter/10.1007/3-540-28993-3_7         *)
(* The connection between the two definition is not worked out yet *)
Definition homology_alt_pres := (pres (quot_by phi)).-ker (kernel psi).

Lemma homology_dvd : homology_alt_pres %| pres homology.
Proof.
rewrite /homology /homology_alt_pres.
rewrite dvd_mx_col /= !dvd_ker dvd_quot_mx ?ker_modK //=.
rewrite -[X in _ %| X](subrK phi%:m) dvdmxDl ?dvd_col_mxl //=.
rewrite (dvdmx_trans (dvd_col_mxu _ _)) //.
have := @factorP _ _ _ [Mono of kernel psi] phi.
rewrite /eqmor /= subr0 mulmx1; apply.
rewrite (dvdmx_trans (dvd_col_mxl _ _)) // dvd_ker.
by move: mul_phi_psi; rewrite /eqmor subr0.
Qed.

(* Lemma homology_alt_dvd : pres homology %| homology_alt_pres. *)
(* Proof. *)
(* rewrite /homology /homology_alt_pres /=. *)
(* have factor_phi := @factorP _ _ _ [Mono of kernel psi] phi. *)
(* rewrite /eqmor /= subr0 mulmx1 in factor_phi. *)
(* apply/dvd_col_mxP => /=. *)
(* eexists. *)
(* (* rewrite (dvdmx_trans (dvd_col_mxu _ _)) //. *) *)
(* rewrite dvdmxB // !dvd_ker /=. *)
(* Abort. *)

End homology.

End theory.

Notation "phi %/ psi" := (quot_by (factor phi psi)).

Section smith_fpmod.

Local Open Scope mxpresentation_scope.

Variable R : edrType.

Variable M : {fpmod R}.

Let D := FPmod (diag_mx (pres M)).
Let P := (smith (pres M)).1.1.
Let Q := (smith (pres M)).2.

(*           M         *)
(*         ----->      *)
(*        |      |     *)
(*   P^-1 |      | Q   *)
(*        v  D   v     *)
(*         ----->      *)
Fact smith_subproof : pres D %| pres M *m Q.
Proof.
apply/dvdmxP; exists (invmx P).
by rewrite /D mulmx_diag_mx mulmxA mulKVmx ?col_ebase_unit // /row_ebase invmxK.
Qed.

Definition smithm : 'Mor(M, D) := Morphism smith_subproof.

Fact smith_inv_subproof : pres M %| pres D *m invmx Q.
Proof.
apply/dvdmxP; exists P.
by rewrite /D mulmx_diag_mx mulmxKV ?row_ebase_unit // /col_ebase invmxK.
Qed.

Definition smithm_inv : 'Mor(D, M) := Morphism smith_inv_subproof.

Lemma iso_smithm : isomorphisms smithm smithm_inv.
Proof.
have hQ_unit : Q \in unitmx by rewrite /Q; case: smithP.
by rewrite /isomorphisms /eqmor /= ?(mulmxV,mulVmx,subrr,dvdmx0).
Qed.

Canonical smith_iso : 'Iso(M, D) := iso_of_isom iso_smithm.

End smith_fpmod.
