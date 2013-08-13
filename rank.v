(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import ssralg fintype fingroup perm.
Require Import matrix bigop zmodp mxalgebra.

Require Import refinements (* seqmatrix *) ssrcomplements.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Section FieldRank.

Import Refinements.Op.

Local Open Scope hetero_computable_scope.
Local Open Scope computable_scope.

Variable A : Type.
Variable mxA : nat -> nat -> Type.
Variable ordA : nat -> Type.

Notation "''M_' ( m , n )" := (mxA m n) : type_scope.
Notation "''M_' n" := (mxA n n) : type_scope.

Context `{zero A, eq A, inv A, fun_of A ordA mxA}.
Context `{forall m, zero (ordA (1 + m))}.
Context `{row_class ordA mxA, row'_class ordA mxA, !hmul mxA, rsub mxA}.
Context `{!hsub mxA, forall m n, scale A (mxA m n), lsub mxA}.

Variable find_pivot : forall m n, mxA m n.+1 -> option (ordA m).

Fixpoint rank_elim {m n : nat} : mxA m n -> nat :=
  match n return mxA m n -> nat with
  | p.+1 => fun (M : mxA m (1 + p)) =>
    if find_pivot M is Some k then
      let a := fun_of_matrix M k 0 in
      let u := rsubmx (row k M) in
      let R := row' k M in
      let v := a^-1 *: lsubmx R in
      let R := (rsubmx R - v *m u)%HC in
      (1 + rank_elim R)%N
    else rank_elim (rsubmx M)
  | _ => fun _ => 0%N
  end.

End FieldRank.

Section rank_correctness.

Import Refinements.
Import GRing.Theory.

Local Open Scope ring_scope.

Variable F : fieldType.

Instance : Op.zero F := 0%R.
Instance : Op.inv F := GRing.inv.
Instance : forall m n, Op.scale F 'M[F]_(m,n) :=
  fun m n => (@GRing.scale _ _).
Instance : Op.fun_of F ordinal (matrix F) := (@fun_of_matrix F).

Instance : forall m, Op.zero (ordinal (1 + m)) := fun _ => 0%R.

Instance : Op.hadd (matrix F) := @addmx F.
Instance : Op.hsub (matrix F) := (fun _ _ M N => M - N).
Instance : Op.hmul (matrix F) := @mulmx F.
Instance : Op.lsub (matrix F) := @matrix.lsubmx F.
Instance : Op.rsub (matrix F) := @matrix.rsubmx F.
Instance : Op.block (matrix F) := @matrix.block_mx F.

Instance : Op.row_class ordinal (matrix F) := (@row F).
Instance : Op.row'_class ordinal (matrix F) := (@row' F).

Lemma rank_row0mx (m n p : nat) (M : 'M[F]_(m,n)) :
  \rank (row_mx (0: 'M[F]_(m,p)) M) = \rank M.
Proof. by rewrite -mxrank_tr tr_row_mx trmx0 -addsmxE adds0mx mxrank_tr. Qed.

Lemma rank_block0dl m n a Aur (Adr : 'M[F]_(m,n)) :
  a != 0 -> \rank (block_mx (a%:M : 'M_1) Aur 0 Adr) = (1 + \rank Adr)%N.
Proof.
move=> nz_a.
rewrite /block_mx -addsmxE mxrank_disjoint_sum.
  rewrite rank_row0mx rank_rV.
  have->//: row_mx a%:M Aur != 0.
    apply/eqP; move/matrixP/(_ 0 0); rewrite !mxE.
    by case: splitP => // j _; rewrite ord1 !mxE; move/eqP: nz_a.
  apply/eqP/rowV0P=> v0; rewrite sub_capmx; case/andP=> /sub_rVP [k Hv0k].
  rewrite Hv0k; case/submxP=> D; move/matrixP/(_ 0 0); rewrite !mxE.
  case: splitP=> // j _; rewrite ord1 mxE mulr1n big1.
  by move/eqP; rewrite mulf_eq0 (negbTE nz_a) orbF; move/eqP ->; rewrite scale0r.
by move=> i _; rewrite !mxE; case: splitP=> // l _; rewrite mxE mulr0.
Qed.

Lemma row'_row_perm m n (M : 'M[F]_(1 + m, n)) k :
  row' k M = dsubmx (row_perm (lift_perm 0 k 1%g) M : 'M_(1 + m, n)).
Proof.
by apply/matrixP=> i j; rewrite !mxE rshift1 lift_perm_lift perm1.
Qed.

Lemma row_row_perm m n (M : 'M[F]_(1 + m, n)) k :
  row k M = @usubmx _ 1 _ _ (row_perm (lift_perm 0 k 1%g) M).
Proof.
by apply/matrixP=> i j; rewrite !mxE ord1 lshift0 lift_perm_id.
Qed.

Variable find_pivot : forall m n, 'M[F]_(m,n.+1) -> option 'I_m.

Hypothesis find_pivotP : forall m n (M : 'M_(m, n.+1)),
  pick_spec [pred k | M k 0 != 0] (find_pivot M).

Lemma rank_elimP m n (M : 'M[F]_(m,n)) : rank_elim find_pivot M = \rank M.
Proof.
elim: n m M => [m M|n IHn m]; first by rewrite thinmx0 mxrank0.
rewrite -[n.+1]/(1 + n)%N => M /=.
have [|nz_Mk0] /= := find_pivotP; last first.
  rewrite -{2}[M]hsubmxK.
  have->: lsubmx M = 0.
    apply/matrixP => i j; rewrite !mxE ord1 lshift0.
    by have /(_ i)/negbFE/eqP -> := nz_Mk0.
  by rewrite rank_row0mx.
case: m M => [M []|m] //.
rewrite -[m.+1]/(1 + m)%N => M k /= nz_Mk0; rewrite IHn.
pose P : 'M[F]_(1 + m) := perm_mx (lift_perm 0 k 1%g).
have->: \rank M = \rank (P *m M).
  by rewrite eqmxMfull // row_full_unit unitmx_perm.
rewrite -row_permE.
set xM : 'M[F]_(1 + m, 1 + n) := row_perm _ _.
pose D : 'M[F]_(1 + m) := block_mx 1%:M 0 (- (M k 0)^-1 *: (dlsubmx xM)) 1%:M.
have hD : row_full D.
  by rewrite row_full_unit unitmxE !det_lblock !det1 !mul1r unitr1.
rewrite -(eqmxMfull xM hD) -[xM]submxK mulmx_block !mul1mx !mul0mx !addr0.
rewrite scaleNr mulNmx [ulsubmx xM]mx11_scalar !mxE !lshift0 lift_perm_id.
rewrite mul_mx_scalar scalerA divrr ?unitfE // scale1r addNr rank_block0dl //.
rewrite {3}/xM /drsubmx /dlsubmx. -row'_row_perm addrC /ursubmx -row_row_perm.
by rewrite mulNmx.
Qed.

End rank_correctness.

Arguments rank_elim A mxA ordA {_ _ _ _ _ _ _ _ _ _} _ m n _.

Section rank_param.

Import Refinements.Op.

Local Open Scope ring_scope.

Variable F : fieldType.

Context (mxA : nat -> nat -> Type) (ordA : nat -> Type)
        (RmxA : forall {m n}, 'M[F]_(m, n) -> mxA m n -> Prop)
        (RordA : forall m, 'I_m -> ordA m -> Prop).

Arguments RmxA {m n} _ _.
Arguments RordA {m} _ _.

Context `{!hadd mxA, !hsub mxA, !hmul mxA, !lsub mxA, !rsub mxA}.
Context `{row_class ordA mxA, row'_class ordA mxA, fun_of F ordA mxA}.
Context `{forall m, zero (ordA (1 + m))}.
Context `{find_pivotC : forall m n : nat, mxA m n.+1 -> option (ordA m)}.

Context `{forall m n : nat, scale F (mxA m n)}.

Instance : zero F := 0%R.
Instance : inv F := GRing.inv.
Instance : forall m n, scale F 'M[F]_(m,n) :=
  fun m n => (@GRing.scale _ _).
Instance : fun_of F ordinal (matrix F) :=
  @matrix.fun_of_matrix F.

Instance : forall m, zero (ordinal (1 + m)) := fun _ => 0%R.

Instance : hadd (matrix F) := @addmx F.
Instance : hsub (matrix F) := (fun _ _ M N => M - N).
Instance : hmul (matrix F) := @mulmx F.
Instance : lsub (matrix F) := @matrix.lsubmx F.
Instance : rsub (matrix F) := @matrix.rsubmx F.
Instance : block (matrix F) := @matrix.block_mx F.

Instance : row_class ordinal (matrix F) := (@matrix.row F).
Instance : row'_class ordinal (matrix F) := (@matrix.row' F).

Fixpoint find_pivot_rec k {m n} (M : 'M[F]_(m.+1,n.+1)) :=
  if k is k'.+1 return option 'I_m.+1 then
    if M (inord (m - k)) 0 != 0 then Some (inord (m - k))
    else find_pivot_rec k' M
  else None.

Definition find_pivot m n :=
  if m is m'.+1 return 'M_(m,n.+1) -> option 'I_m then
    find_pivot_rec m
  else fun _ => None.

Context `{forall m n, param (RmxA ==> RmxA ==> RmxA) +%R
  (@hadd_op _ _ _ m n)}.
Context `{forall m n, param (RmxA ==> RmxA ==> RmxA) (@hsub_op _ _ _ m n)
  (@hsub_op _ _ _ m n)}.
Context `{forall m n p, param (RmxA ==> RmxA ==> RmxA) (@mulmx F m n p)
  (@hmul_op _ _ _ m n p)}.
Context `{forall m n m', param (RmxA ==> RmxA)
  (@matrix.lsubmx F m n m') (@lsubmx _ _ m n m')}.
Context `{forall m n m', param (RmxA ==> RmxA)
  (@matrix.rsubmx F m n m') (@rsubmx _ _ m n m')}.

Context `{forall m n, param (RmxA ==> RordA ==> RordA ==> Logic.eq)
  (@matrix.fun_of_matrix F m n) (@fun_of_matrix _ _ _ _ m n)}.

Context `{forall m n, param (RmxA ==> ohrel RordA)
  (@find_pivot m n) (@find_pivotC m n)}.

Context `{forall m n, param (RordA ==> RmxA ==> RmxA)
  (@matrix.row F m n) (@row _ _ _ m n)}.

Context `{forall m n, param (RordA ==> RmxA ==> RmxA)
  (@matrix.row' F m n) (@row' _ _ _ m n)}.

Context `{forall m n, param (Logic.eq ==> @RmxA m n ==> RmxA)
  (@GRing.scale _ _) (@scale_op _ _ _)}.

Context `{!param (Logic.eq ==> Logic.eq)
  (@GRing.inv _) (@inv_op _ _)}.

Context `{forall m, param (@RordA (1 + m)) 0%R 0%C}.

Instance param_addn : param (Logic.eq ==> Logic.eq ==> Logic.eq) addn addn.
by rewrite paramE => * ? ? -> ? ? ->.
Qed.

Typeclasses eauto := debug.

Hint Extern 1 (getparam _ _ _) =>
  eapply param_Some : typeclass_instances.

Global Instance param_rank_elim m n :
   param (RmxA ==> Logic.eq)%rel
         (rank_elim F (matrix F) ordinal find_pivot m n)
         (rank_elim F mxA ordA find_pivotC m n).
Proof.
elim: n m => [|n IHn] m; first exact: get_param.
rewrite /=.
eapply param_abstr=> x a param_xa.
move: (H10 m n).
move: (param_xa) => ?.
rewrite 2!paramE in param_xa *.
move/(_ x a param_xa) => /=.
case: (find_pivot x) => [?|].
case: (find_pivotC a) => pa //=.
rewrite -[RordA]paramE => RordAxpa.
eapply param_apply.
  eapply param_apply; first exact param_addn.
  exact: param_eq.
eapply param_apply.
by tc.
eapply param_apply.
eapply param_apply.
by eapply H5.
eapply param_apply.
by eapply H8.
eapply param_apply.
eapply param_apply.
by eapply H12.
by tc.
by tc.
eapply param_apply.
eapply param_apply.
by eapply H6.
eapply param_apply.
eapply param_apply.
by eapply H13.

eapply param_apply.
by eapply param0.
eapply param_apply.
eapply param_apply.
eapply param_apply.
by eapply H9.
exact: get_param.
exact: get_param.
exact: get_param.
eapply param_apply.
by eapply H7.
eapply param_apply.
by tc.
by tc.

eapply param_apply.
by tc.
eapply param_apply.
by tc.
by tc.

case: (find_pivotC a) => // _.
eapply param_apply.
by tc.
eapply param_apply.
by tc.
by tc.
Qed.

(*
Notation "n %:F2" := (n%R : 'F_2) (at level 2, left associativity, format "n %:F2").

Definition M := [::
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2];
[:: 0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;1%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;0%:F2;1%:F2;1%:F2]
].


Eval vm_compute in (size M).

Eval vm_compute in (size (head [::] M)).

Time Eval vm_compute in (rank 9 348 M).

*)
