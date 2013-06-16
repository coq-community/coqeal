(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ZArith Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements.

Instance Zops (R : ringType) (n : nat) : @Ring_ops 'M[R]_n 0%R
  (scalar_mx 1) (@addmx R _ _) mulmx (fun M N => addmx M (oppmx N)) (@oppmx R _ _) eq.

Instance Zr (R : ringType) (n : nat) : (@Ring _ _ _ _ _ _ _ _ (Zops R n)).
Proof.
constructor=> //.
  + exact:eq_equivalence.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1; rewrite H1.
  + exact:add0mx.
  + exact:addmxC.
  + exact:addmxA.
  + exact:mul1mx.
  + exact:mulmx1.
  + exact:mulmxA.
  + exact:mulmxDl.
  + by move=> M N P ; exact:mulmxDr.
  + by move=> M; rewrite /addition /add_notation (addmxC M) addNmx.
Qed.

Section Strassen_generic.

Local Open Scope ring_scope.

(** K is the size threshold below which we switch back to naive
multiplication *)
Let K := 32%positive.

Local Coercion nat_of_pos : positive >-> nat.

Lemma addpp p : xO p = (p + p)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addSpp p : xI p = (p + p).+1%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addp1 p : xI p = (xO p + 1)%N :> nat.
Proof. by rewrite addn1. Qed.

Lemma addpp1 p : xI p = (p + p + 1)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn addn1. Qed.

Lemma lt0p : forall p : positive, 0 < p.
Proof.
by elim=> // p IHp /=; rewrite NatTrec.doubleE -addnn; exact:ltn_addl.
Qed.

Import Refinements.Op.

Variable mxA : nat -> nat -> Type.

Context `{!hadd mxA, !hsub mxA, !hmul mxA, !hcast mxA}.
Context `{!ulsub mxA, !ursub mxA, !dlsub mxA, !drsub mxA, !block mxA}.

Definition Strassen_step {p : positive} (A B : mxA (p + p) (p + p))
  (f : mxA p p -> mxA p p -> mxA p p) : mxA (p + p) (p + p) :=
  let A11 := ulsubmx A in
  let A12 := ursubmx A in
  let A21 := dlsubmx A in
  let A22 := drsubmx A in
  let B11 := ulsubmx B in
  let B12 := ursubmx B in
  let B21 := dlsubmx B in
  let B22 := drsubmx B in
  let X := hsub_op A11 A21 in
  let Y := hsub_op B22 B12 in
  let C21 := f X Y in
  let X := hadd_op A21 A22 in
  let Y := hsub_op B12 B11 in
  let C22 := f X Y in
  let X := hsub_op X A11 in
  let Y := hsub_op B22 Y in
  let C12 := f X Y in
  let X := hsub_op A12 X in
  let C11 := f X B22 in
  let X := f A11 B11 in
  let C12 := hadd_op X C12 in
  let C21 := hadd_op C12 C21 in
  let C12 := hadd_op C12 C22 in
  let C22 := hadd_op C21 C22 in
  let C12 := hadd_op C12 C11 in
  let Y := hsub_op Y B21 in
  let C11 := f A22 Y in
  let C21 := hsub_op C21 C11 in
  let C11 := f A12 B21 in
  let C11 := hadd_op X C11 in
  block_mx C11 C12 C21 C22.

Definition Strassen_xO {p : positive} Strassen_p :=
  fun A B =>
    if p <= K then hmul_op A B else
    let A := hcast_op (addpp p,addpp p) A in
    let B := hcast_op (addpp p,addpp p) B in
    hcast_op (esym (addpp p), esym (addpp p)) (Strassen_step A B Strassen_p).
  
Definition Strassen_xI {p : positive} Strassen_p :=
   fun M N =>
    if p <= K then hmul_op M N else
    let M := hcast_op (addpp1 p, addpp1 p) M in
    let N := hcast_op (addpp1 p, addpp1 p) N in
    let M11 := ulsubmx M in
    let M12 := ursubmx M in
    let M21 := dlsubmx M in
    let M22 := drsubmx M in
    let N11 := ulsubmx N in
    let N12 := ursubmx N in
    let N21 := dlsubmx N in
    let N22 := drsubmx N in
    let C := hadd_op (Strassen_step M11 N11 Strassen_p) (hmul_op M12 N21) in
    let R12 := hadd_op (hmul_op M11 N12) (hmul_op M12 N22) in
    let R21 := hadd_op (hmul_op M21 N11) (hmul_op M22 N21) in
    let R22 := hadd_op (hmul_op M21 N12) (hmul_op M22 N22) in
    hcast_op (esym (addpp1 p), esym (addpp1 p)) (block_mx C R12 R21 R22).

Definition Strassen := 
  (positive_rect (fun p => (mxA p p -> mxA p p -> mxA p p))
                 (@Strassen_xI) (@Strassen_xO) (fun M N => hmul_op M N)).

End Strassen_generic.

Arguments Strassen_step {mxA _ _ _ _ _ _ _ p} A B f.
Arguments Strassen {mxA _ _ _ _ _ _ _ _ _ p} M N.

Section Strassen_correctness.

Import Refinements.Op.

Variable R : ringType.

Local Coercion nat_of_pos : positive >-> nat.

Local Open Scope ring_scope.

Instance : hadd (matrix R) := @addmx R.
Instance : hsub (matrix R) := (fun _ _ M N => addmx M (oppmx N)).
Instance : hmul (matrix R) := @mulmx R.
Instance : hcast (matrix R) := @castmx R.
Instance : ulsub (matrix R) := @matrix.ulsubmx R.
Instance : ursub (matrix R) := @matrix.ursubmx R.
Instance : dlsub (matrix R) := @matrix.dlsubmx R.
Instance : drsub (matrix R) := @matrix.drsubmx R.
Instance : block (matrix R) := @matrix.block_mx R.

Lemma Strassen_stepP (p : positive) (A B : 'M[R]_(p + p)) f :
  f =2 mulmx -> Strassen_step A B f = A *m B.
Proof.
move=> Hf; rewrite -{2}[A]submxK -{2}[B]submxK mulmx_block /Strassen_step !Hf.
rewrite /GRing.add /= /GRing.opp /=.
by congr block_mx; non_commutative_ring.
Qed.

Lemma mulmx_cast {R' : ringType} {m n p m' n' p'} {M:'M[R']_(m,p)} {N:'M_(p,n)}
  {eqm : m = m'} (eqp : p = p') {eqn : n = n'} :
  castmx (eqm,eqn) (M *m N) = castmx (eqm,eqp) M *m castmx (eqp,eqn) N.
Proof. by case eqm ; case eqn ; case eqp. Qed.

Lemma StrassenP p : param (Logic.eq ==> Logic.eq ==> Logic.eq) mulmx (Strassen (p := p)).
Proof.
rewrite paramE => a _ <- b _ <-.
elim: p a b => // [p IHp|p IHp] M N.
  rewrite /= /Strassen_xI; case:ifP=> // _.
  by simpC; rewrite Strassen_stepP // -mulmx_block !submxK -mulmx_cast castmxK.
rewrite /= /Strassen_xO; case:ifP=> // _.
by simpC; rewrite Strassen_stepP // -mulmx_cast castmxK.
Qed.

End Strassen_correctness.

Section strassen_param.

Import Refinements.Op.

Local Coercion nat_of_pos : positive >-> nat.

Context (A : ringType) (C : Type) (RA : A -> C -> Prop).
Context (mxC : nat -> nat -> Type)
        (RmxA : forall {m n}, 'M[A]_(m, n) -> mxC m n -> Prop).
Arguments RmxA {m n} _ _.

Context `{!hadd mxC, !hsub mxC, !hmul mxC, !hcast mxC}.
Context `{!ulsub mxC, !ursub mxC, !dlsub mxC, !drsub mxC, !block mxC}.

Instance : hadd (matrix A) := @addmx A.
Instance : hsub (matrix A) := (fun _ _ M N => addmx M (oppmx N)).
Instance : hmul (matrix A) := @mulmx A.
Instance : hcast (matrix A) := @castmx A.
Instance : ulsub (matrix A) := @matrix.ulsubmx A.
Instance : ursub (matrix A) := @matrix.ursubmx A.
Instance : dlsub (matrix A) := @matrix.dlsubmx A.
Instance : drsub (matrix A) := @matrix.drsubmx A.
Instance : block (matrix A) := @matrix.block_mx A.

Context `{forall m n, param (RmxA ==> RmxA ==> RmxA) (@addmx A m n)
  (@hadd_op _ _ _ m n)}.
Context `{forall m n, param (RmxA ==> RmxA ==> RmxA) (@hsub_op _ _ _ m n)
  (@hsub_op _ _ _ m n)}.
Context `{forall m n p, param (RmxA ==> RmxA ==> RmxA) (@mulmx A m n p)
  (@hmul_op _ _ _ m n p)}.
Context `{forall m n m' n' p, param (RmxA ==> RmxA) (@castmx A m n m' n' p)
  (@hcast_op _ _ _ m n m' n' p)}.
Context `{forall m n m' n', param (RmxA ==> RmxA ==> RmxA ==> RmxA ==> RmxA)
  (@matrix.block_mx A m n m' n')  (@block_mx _ _ m n m' n')}.
Context `{forall m n m' n', param (RmxA ==> RmxA)
  (@matrix.drsubmx A m n m' n')  (@drsubmx _ _ m n m' n')}.
Context `{forall m n m' n', param (RmxA ==> RmxA)
  (@matrix.ursubmx A m n m' n')  (@ursubmx _ _ m n m' n')}.
Context `{forall m n m' n', param (RmxA ==> RmxA)
  (@matrix.dlsubmx A m n m' n')  (@dlsubmx _ _ m n m' n')}.
Context `{forall m n m' n', param (RmxA ==> RmxA)
  (@matrix.ulsubmx A m n m' n')  (@ulsubmx _ _ m n m' n')}.

Instance param_elim_positive P P' (R : forall p, P p -> P' p -> Prop) 
  txI txI' txO txO' txH txH' : 
  (forall p, getparam (R p ==> R (p~1)%positive) (txI p) (txI' p)) ->
  (forall p, getparam (R p ==> R (p~0)%positive) (txO p) (txO' p)) ->
  (getparam (R 1%positive) txH txH') ->
  forall p, getparam (R p) (positive_rect P txI  txO  txH p)
                        (positive_rect P' txI' txO' txH' p).
Proof.
rewrite paramE => RI RO RH.
elim => [p ihp|p ihp|]; rewrite ?paramE //.
  by have := RI p; rewrite !paramE in ihp *; apply.
by have := RO p; rewrite !paramE in ihp *; apply.
Qed.

Instance param_eq T (x : T) : param Logic.eq x x.
Proof. by rewrite paramE. Qed.

Existing Instance StrassenP.

Global Instance param_Strassen_step p :
   param (RmxA ==> RmxA ==> (RmxA ==> RmxA ==> RmxA) ==> RmxA)%rel
         (@Strassen_step (@matrix A) _ _ _ _ _ _ _ p)
         (@Strassen_step mxC _ _ _ _ _ _ _ p).
Proof. by rewrite /Strassen_step; apply: get_param. Qed.

Global Instance refines_Strassen p :
   param (RmxA ==> RmxA ==> RmxA)%rel
         (@Strassen (@matrix A)  _ _ _ _ _ _ _ _ _ p)
         (@Strassen mxC _ _ _ _ _ _ _ _ _ p).
Proof.
rewrite /Strassen /Strassen_xI /Strassen_xO; eapply get_param.
rewrite -[X in getparam X]/((fun p : positive =>
         @RmxA p p ==> @RmxA p p ==> @RmxA p p)%rel p).
by apply (param_elim_positive (fun _ => _) (fun _ => _)); tc.
Qed.

End strassen_param.
