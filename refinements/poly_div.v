(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

From CoqEAL Require Import param refinements hrel poly_op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

Section generic_division.

Variable N R polyR : Type.
Context `{lt_of N, sub_of N, add_of N, one_of N, zero_of N, spec_of N nat}.
Context `{size_of polyR N, lead_coef_of R polyR, cast_of R polyR}.
Context `{shift_of polyR N, add_of polyR, mul_of polyR, sub_of polyR}.
Context `{eq_of polyR, zero_of polyR}.

Definition div_rec_poly (q : polyR) :=
  let sq := (size_op q : N) in
  let cq := (cast (lead_coef_op q : R) : polyR) in
  fix loop (k : N) (qq r : polyR) (n : nat) {struct n} :=
    if (size_op r < sq)%C
    then (k, qq, r) else
      let m := shift_op (size_op r - sq)%C
                        (cast (lead_coef_op r : R) : polyR) in
      let qq1 := (qq * cq + m)%C in
      let r1 := (r * cq - m * q)%C in
      if n is n1.+1 then loop (k + 1)%C qq1 r1 n1 else ((k + 1)%C, qq1, r1).

Global Instance div_poly : div_of polyR :=
  fun p q => (if (q == 0)%C
                 then (0%C, 0%C, p)
                 else div_rec_poly q 0%C 0%C p (spec (size_op p : N))).1.2.

Global Instance mod_poly : mod_of polyR :=
  fun p q => (if (q == 0)%C
                 then (0%C, 0%C, p)
                 else div_rec_poly q 0%C 0%C p (spec (size_op p : N))).2.

Global Instance scal_poly : scal_of polyR N :=
  fun p q => (if (q == 0)%C then (0%C, 0%C, p)
              else div_rec_poly q 0%C 0%C p (spec (size_op p : N))).1.1.

End generic_division.

Parametricity div_rec_poly.
Parametricity div_poly.
Parametricity mod_poly.
Parametricity scal_poly.

Section division_correctness.

Variable R : ringType.

Local Instance lt_nat : lt_of nat := ltn.
Local Instance sub_nat : sub_of nat := subn.
Local Instance add_nat : add_of nat := addn.
Local Instance one_nat : one_of nat := 1%N.
Local Instance zero_nat : zero_of nat := 0%N.
Local Instance spec_nat : spec_of nat nat := spec_id.

Local Instance size_of_poly : size_of {poly R} nat := sizep (R:=R).
Local Instance lead_coef_poly : lead_coef_of R {poly R} := lead_coef.
Local Instance cast_poly : cast_of R {poly R} := polyC.
Local Instance shift_poly : shift_of {poly R} nat := shiftp (R:=R).
Local Instance add_poly : add_of {poly R} := +%R.
Local Instance mul_poly : mul_of {poly R} := *%R.
Local Instance sub_poly : sub_of {poly R} := fun p q => p - q.
Local Instance eq_poly : eq_of {poly R} := eqtype.eq_op.
Local Instance zero_poly : zero_of {poly R} := 0%R.

Lemma div_rec_polyE (p q : {poly R}) n r m:
  div_rec_poly (N:=nat) (R:=R) q n r p m = redivp_rec q n r p m.
Proof.
  rewrite /div_rec_poly /redivp_rec.
  move: n r p.
  elim: m=> [|m ihm] n r p;
    by rewrite -[(_ < _)%C]/(_ < _) /shift_op /shift_poly /shiftp ?ihm mul_polyC
               [(_ + _)%C]addn1.
Qed.

Lemma div_polyE (p q : {poly R}) : div_poly (N:=nat) (R:=R) p q = rdivp p q.
Proof.
  rewrite /div_poly -[rdivp p q]/((rscalp p q, rdivp p q, rmodp p q).1.2).
  rewrite -redivp_def div_rec_polyE /redivp /redivp_expanded_def.
  by rewrite unlock /= /spec_nat /spec_id.
Qed.

Lemma mod_polyE (p q : {poly R}) : mod_poly (N:=nat) (R:=R) p q = rmodp p q.
Proof.
  rewrite /mod_poly -[rmodp p q]/((rscalp p q, rdivp p q, rmodp p q).2).
  rewrite -redivp_def div_rec_polyE /redivp /redivp_expanded_def.
  by rewrite unlock /= /spec_nat /spec_id.
Qed.

Lemma scal_polyE (p q : {poly R}) : scal_poly (N:=nat) (R:=R) p q = rscalp p q.
Proof.
  rewrite /scal_poly -[rscalp p q]/((rscalp p q, rdivp p q, rmodp p q).1.1).
  rewrite -redivp_def div_rec_polyE /redivp /redivp_expanded_def.
  by rewrite unlock /= /spec_nat /spec_id.
Qed.

Section division_param.

Local Open Scope rel_scope.

Context (N : Type) (rN : nat -> N -> Type).
Context (C : Type) (rC : R -> C -> Type).
Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).

Context `{lt_of N, sub_of N, add_of N, one_of N, zero_of N, spec_of N nat}.
Context `{size_of polyC N, lead_coef_of C polyC, cast_of C polyC}.
Context `{shift_of polyC N, add_of polyC, mul_of polyC, sub_of polyC}.
Context `{eq_of polyC, zero_of polyC}.
Context `{!refines (rN ==> rN ==> bool_R) ltn lt_op}.
Context `{!refines (rN ==> rN ==> rN) subn sub_op}.
Context `{!refines (rN ==> rN ==> rN) addn add_op}.
Context `{!refines rN 1%N 1%C, !refines rN 0%N 0%C}.
Context `{!refines (rN ==> nat_R) spec_id spec}.
Context `{!refines (RpolyC ==> rN) size_op size_op}.
Context `{!refines (RpolyC ==> rC) lead_coef_poly lead_coef_op}.
Context `{!refines (rC ==> RpolyC) cast_poly cast}.
Context `{!refines (rN ==> RpolyC ==> RpolyC) shift_poly shift_op}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) +%R +%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) *%R *%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) sub_poly sub_op}.
Context `{!refines (RpolyC ==> RpolyC ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines RpolyC 0%R 0%C}.

Global Instance RpolyC_div_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC)
          (div_poly (N:=nat) (R:=R) (polyR:={poly R}))
          (div_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof. param div_poly_R. Qed.

Global Instance refine_div_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC) (@rdivp R)
          (div_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  rewrite -div_polyE.
  exact: refinesP.
Qed.

Global Instance RpolyC_mod_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC)
          (mod_poly (N:=nat) (R:=R) (polyR:={poly R}))
          (mod_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof. param mod_poly_R. Qed.

Global Instance refine_mod_poly :
  refines (RpolyC ==> RpolyC ==> RpolyC) (@rmodp R)
          (mod_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  rewrite -mod_polyE.
  exact: refinesP.
Qed.

Global Instance RpolyC_scal_poly :
  refines (RpolyC ==> RpolyC ==> rN)
          (scal_poly (N:=nat) (R:=R) (polyR:={poly R}))
          (scal_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  eapply (scal_poly_R (polyR_R:=RpolyC))=> // *;
  eapply refinesP;
  do ?eapply refines_apply; tc.
Qed.

Global Instance refine_scal_poly :
  refines (RpolyC ==> RpolyC ==> rN) (@rscalp R)
          (scal_poly (N:=N) (R:=C) (polyR:=polyC)).
Proof.
  rewrite refinesE=> p p' hp q q' hq.
  rewrite -scal_polyE.
  exact: refinesP.
Qed.

End division_param.
End division_correctness.