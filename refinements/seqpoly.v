From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

From CoqEAL Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op.

Local Open Scope ring_scope.

(* Specific classes for polynomials *)
Section classes.

Class shift_of polyA := shift_op : nat -> polyA -> polyA.
Hint Mode shift_of + : typeclass_instances.
Class split_of polyA := split_op : nat -> polyA -> polyA * polyA.
Hint Mode split_of + : typeclass_instances.
Class size_of polyA := size_op : polyA -> nat.
Hint Mode size_of + : typeclass_instances.
Class lead_coef_of A polyA := lead_coef_op : polyA -> A.
Hint Mode lead_coef_of + + : typeclass_instances.

End classes.

Typeclasses Transparent shift_of split_of size_of lead_coef_of.

Section seqpoly_op.

Local Open Scope computable_scope.

Variable A : Type.

Definition seqpoly := seq A.

Context `{zero_of A, one_of A}.
Context `{add_of A, opp_of A, sub_of A, mul_of A, eq_of A}.

Global Instance cast_seqpoly : cast_of A seqpoly := fun x => [:: x].

Global Instance seqpoly0 : zero_of seqpoly := [::].
Global Instance seqpoly1 : one_of seqpoly := [:: 1].
Global Instance opp_seqpoly : opp_of seqpoly := List.map -%C.

Fixpoint add_seqpoly_fun (p q : seqpoly) : seqpoly := match p,q with
  | [::], q => q
  | p, [::] => p
  | a :: p', b :: q' => a + b :: add_seqpoly_fun p' q'
  end.

Global Instance add_seqpoly : add_of seqpoly := add_seqpoly_fun.
Global Instance sub_seqpoly : sub_of seqpoly := fun x y => (x + - y)%C.

Global Instance scale_seqpoly : scale_of A seqpoly := fun a => map ( *%C a).

(* 0%C :: aux p = shift 1 (aux p) *)
Global Instance mul_seqpoly : mul_of seqpoly := fun p q =>
  let fix aux p :=
      if p is a :: p then (a *: q + (0%C :: aux p))%C else 0
  in aux p.

Global Instance size_seqpoly : size_of seqpoly :=
  let fix aux p :=
      if p is a :: p then
        let sp := aux p in
        if (eqn sp 0)%nat then ~~ (a == 0)%C : nat else sp.+1
      else 0%nat in aux.

Global Instance eq_seqpoly : eq_of seqpoly :=
  fun p q => all (fun x => x == 0)%C (p - q)%C.

Global Instance shift_seqpoly : shift_of seqpoly :=
  fun n => ncons n 0%C.

Global Instance split_seqpoly : split_of seqpoly :=
  fun n p => (drop n p,take n p).

Global Instance lead_coef_seqpoly : lead_coef_of A seqpoly :=
  fun p => nth 0 p (size_seqpoly p).-1.

(* pseudo-division *)
Definition div_rec_seqpoly (q : seqpoly) :=
  let sq := size_seqpoly q in
  let cq := (cast (lead_coef_seqpoly q) : seqpoly) in
  fix loop (k : nat) (qq r : seqpoly) (n : nat) {struct n} :=
    if (size_seqpoly r < sq)%nat then (k, qq, r) else
    let m := shift_seqpoly (size_seqpoly r - sq)%nat
                           (cast (lead_coef_seqpoly r) : seqpoly) in
    let qq1 := (qq * cq + m)%C in
    let r1 := (r * cq - m * q)%C in
    if n is n1.+1 then loop k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

Global Instance div_seqpoly : div_of seqpoly :=
  fun p q => (if (q == 0)%C
                 then (0%nat, 0%C, p)
                 else div_rec_seqpoly q 0 0%C p (size_op p)).1.2.

Global Instance mod_seqpoly : mod_of seqpoly :=
  fun p q => (if (q == 0)%C
                 then (0%nat, 0%C, p)
                 else div_rec_seqpoly q 0 0%C p (size_op p)).2.

Definition scal_seqpoly p q :=
  (if (q == 0)%C then (0%N, 0%C, p)
                 else div_rec_seqpoly q 0 0%C p (size_seqpoly p)).1.1.

End seqpoly_op.

Parametricity cast_seqpoly.
Parametricity seqpoly0.
Parametricity seqpoly1.
Parametricity opp_seqpoly.
Parametricity add_seqpoly.
Parametricity sub_seqpoly.
Parametricity scale_seqpoly.
Parametricity mul_seqpoly.
Parametricity size_seqpoly.
Parametricity eq_seqpoly.
Parametricity shift_seqpoly.
Parametricity split_seqpoly.
Parametricity lead_coef_seqpoly.
Parametricity div_rec_seqpoly.
Parametricity div_seqpoly.
Parametricity mod_seqpoly.
Parametricity scal_seqpoly.

Section seqpoly_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oneR  : one_of R  := 1%R.
Local Instance addR  : add_of R  := +%R.
Local Instance subR  : sub_of R  := fun x y => x - y.
Local Instance mulR  : mul_of R  := *%R.
Local Instance oppR  : opp_of R  := -%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.

Definition splitp : nat -> {poly R} -> {poly R} * {poly R} :=
  fun n p => (rdivp p 'X^n, rmodp p 'X^n).

Definition shiftp n (p : {poly R}) := p * 'X^n.

Definition seqpoly_of_poly (p : {poly R}) : seqpoly R :=
  polyseq p.

Definition poly_of_seqpoly (sp : seqpoly R) : {poly R} :=
  \poly_(i < size sp) nth 0 sp i.

Definition Rseqpoly : {poly R} -> seqpoly R -> Type := fun_hrel poly_of_seqpoly.

Local Open Scope rel_scope.

(* zero and one *)
Local Instance Rseqpoly_0 : refines Rseqpoly 0%R 0%C.
Proof.
  by rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly poly_def big_ord0.
Qed.

Local Instance Rseqpoly_1 : refines Rseqpoly 1%R 1%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly poly_def /=.
  by rewrite zmodp.big_ord1 expr0 alg_polyC [(1%:P)]/(1%C) polyC1.
Qed.

Local Instance Rseqpoly_cons :
  refines (eq ==> Rseqpoly ==> Rseqpoly) (@cons_poly R) cons.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ x -> _ sp <-.
  rewrite cons_poly_def poly_def big_ord_recl /= expr0 alg_polyC addrC.
  rewrite /bump poly_def big_distrl /=.
  apply: congr2=> //.
  apply: eq_bigr=> i _.
  by rewrite -[in RHS]mul_polyC -mulrA -exprSr mul_polyC.
Qed.

Local Instance Rseqpoly_cast : refines (eq ==> Rseqpoly) polyC cast_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ x ->.
  rewrite /cast /cast_seqpoly /= poly_def zmodp.big_ord1 /=.
  by rewrite expr0 alg_polyC.
Qed.

Local Instance Rseqpoly_opp : refines (Rseqpoly ==> Rseqpoly) -%R -%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <-.
  rewrite !poly_def -GRing.sumrN size_map.
  apply: eq_bigr=> i _.
  rewrite -[in RHS]mul_polyC -mulNr -polyC_opp mul_polyC.
  by rewrite (nth_map 0%C).
Qed.

Lemma coef_poly_of_seqpoly (sp : seqpoly R) (i : nat) :
  (\poly_(j < size sp) sp`_j)`_i = sp`_i.
Proof.
  rewrite coef_poly.
  have [iltp|pleqi] := ltnP i (size sp)=> //.
  by rewrite nth_default.
Qed.

Lemma coef_add_seqpoly (sp sq : seqpoly R) (i : nat) :
  (sp + sq)%C`_i = sp`_i + sq`_i.
Proof.
  elim: sp sq i=> [sq i|a p ihp [|b q] [|i]] //=.
        by rewrite [(_ + _)%C]/add_seqpoly /add_seqpoly_fun nth_nil add0r.
      by rewrite addr0.
    by rewrite addr0.
  by rewrite ihp.
Qed.

Local Instance Rseqpoly_add :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) +%R +%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  apply/polyP=> i.
  by rewrite coef_add_poly !coef_poly_of_seqpoly coef_add_seqpoly.
Qed.

Lemma coef_opp_seqpoly (sp : seqpoly R) (i : nat) : (- sp)%C`_i = - sp`_i.
Proof.
  have [iltp|pleqi] := ltnP i (size sp).
    by rewrite (nth_map 0%C).
  by rewrite !nth_default ?oppr0 ?size_map.
Qed.

Local Instance Rseqpoly_sub :
    refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (fun x y => x - y) sub_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  apply/polyP=> i.
  rewrite coef_add_poly coef_opp_poly !coef_poly_of_seqpoly coef_add_seqpoly.
  by rewrite coef_opp_seqpoly.
Qed.

(* scaling *)

Lemma coef_scale_seqpoly (sp : seqpoly R) (a : R) (i : nat) :
  (a *: sp)%C`_i = a * sp`_i.
Proof.
  have [iltp|pleqi] := ltnP i (size sp).
    by rewrite (nth_map 0%C).
  by rewrite !nth_default ?mulr0 ?size_map.
Qed.

Local Instance Rseqpoly_scale :
  refines (eq ==> Rseqpoly ==> Rseqpoly) *:%R *:%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ x -> _ sp <-.
  apply/polyP=> i.
  by rewrite coefZ !coef_poly_of_seqpoly coef_scale_seqpoly.
Qed.

(* multiplication *)
Local Instance Rseqpoly_mul :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) *%R *%C.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  apply/polyP=> i.
  rewrite coef_poly_of_seqpoly.
  elim: sp i=> [i|a p ihp i].
    by rewrite [(_ * _)%C]/mul_seqpoly poly_def big_ord0 mul0r coef0 nth_nil.
  rewrite [(_ * _)%C]/mul_seqpoly coef_add_seqpoly coefM big_ord_recl.
  rewrite !coef_poly_of_seqpoly subn0.
  apply: congr2; first by rewrite coef_scale_seqpoly.
  move: ihp; case: i=> [_|i ihp]; first by rewrite big_ord0.
  rewrite [(_ :: _)`_ _]/= ihp coefM=> {ihp}.
  apply: eq_bigr=> j _.
  by rewrite !coef_poly_of_seqpoly.
Qed.

(* This definition hides the coercion which makes it possible for proof search
   to find Rseqpoly_seqpoly_size *)
Definition sizep : {poly R} -> nat := size.
Lemma sizepE s : sizep s = size s. Proof. by []. Qed.

Lemma poly_cons (p : seqpoly R) (a : R) :
  \poly_(i < size (a :: p)) (a :: p)`_i = a%:P + (\poly_(i < size p) p`_i) * 'X.
Proof.
  rewrite !poly_def big_ord_recl big_distrl /= expr0 alg_polyC /bump /=.
  apply: congr2=> //; apply: eq_bigr=> i _.
  by rewrite add1n exprSr scalerAl.
Qed.

Local Instance Rseqpoly_size :
  refines (Rseqpoly ==> eq) sizep size_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <-.
  rewrite sizepE /size_op.
  elim: sp=> [|a p ihp].
    by rewrite poly_def big_ord0 size_poly0.
  rewrite poly_cons /= -ihp; case sp: (size (\poly_(i < size p) p`_i))=> [|n] /=.
    move /eqP: sp; rewrite size_poly_eq0; move/eqP=> ->.
    by rewrite mul0r addr0 size_polyC.
  rewrite addrC size_addl size_mulX ?sp ?size_polyC; case: (a != 0)=> //;
  by apply/negP; rewrite -size_poly_eq0 sp.
Qed.

Local Instance Rseqpoly_eq :
  refines (Rseqpoly ==> Rseqpoly ==> bool_R) eqtype.eq_op eq_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ sp <- _ sq <-.
  have -> : (\poly_(i < size sp) sp`_i == \poly_(i < size sq) sq`_i)
            = (sp == sq)%C.
    apply/eqP/allP=> [/polyP heq|heq].
      move=> x /(nthP 0%C) [i] hi <-.
      rewrite coef_add_seqpoly coef_opp_seqpoly; simpC.
      by have := (heq i); rewrite !coef_poly_of_seqpoly subr_eq0=> ->.
    apply/polyP=> i; rewrite !coef_poly_of_seqpoly; apply/eqP.
    have [hlt|] := ltnP i (size (sp - sq)%C).
      rewrite -subr_eq0 -coef_opp_seqpoly -coef_add_seqpoly [_ == _]heq //.
      by rewrite mem_nth.
    have -> : size (sp - sq)%C = maxn (size sp) (size sq)=> [{heq}|hleq].
      elim: sp sq=> [sq|a p ihp [|b q]] /=.
          by rewrite max0n [(_ - _)%C]/add_seqpoly /add_seqpoly_fun size_map.
        by rewrite maxn0.
      by rewrite ihp maxnSS.
    by rewrite !nth_default // (leq_trans _ hleq) // leq_max leqnn ?orbT.
  exact: bool_Rxx.
Qed.

(* These can be done with eq instead of nat_R *)
Local Instance Rseqpoly_shift :
  refines (eq ==> Rseqpoly ==> Rseqpoly) shiftp shift_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ n -> _ sp <-.
  apply/polyP=> i.
  rewrite /shiftp coefMXn !coef_poly_of_seqpoly /shift_op /shift_seqpoly.
  by rewrite nth_ncons.
Qed.

Local Instance Rseqpoly_split :
  refines (eq ==> Rseqpoly ==> prod_hrel Rseqpoly Rseqpoly)
          splitp split_op.
Proof.
  rewrite refinesE /Rseqpoly /fun_hrel /poly_of_seqpoly=> _ n -> _ sp <-.
  rewrite /prod_hrel /split_op /split_seqpoly /splitp /=.
  elim: sp n=> [n|a p ihp [|n]].
      by rewrite poly_def big_ord0 rdiv0p rmod0p.
    by rewrite expr0 rdivp1 rmodp1 [\poly_(_ < 0) _]poly_def big_ord0.
  rewrite !poly_cons [\poly_(i < size p) p`_i](@rdivp_eq _ 'X^n) ?monicXn //.
  have [-> ->] := ihp n.
  rewrite mulrDl -mulrA -exprSr addrC -addrA.
  suff htnp :
    size (rmodp (\poly_(i < size p) p`_i) 'X^n * 'X + a%:P) <
    size ('X^n.+1 : {poly R}).
    by rewrite rdivp_addl_mul_small ?rmodp_addl_mul_small ?monicXn // addrC.
  rewrite size_polyXn size_MXaddC ltnS; case: ifP=> // _.
  by rewrite (leq_trans (ltn_rmodpN0 _ _)) ?monic_neq0 ?monicXn ?size_polyXn.
Qed.

Local Instance Rseqpoly_lead_coef :
  refines (Rseqpoly ==> eq) lead_coef lead_coef_op.
Proof.
  rewrite refinesE /lead_coef_op /lead_coef_seqpoly /lead_coef=> p sp hp.
  rewrite -sizepE [sizep _]refines_eq /size_op -hp /poly_of_seqpoly.
  by rewrite coef_poly_of_seqpoly.
Qed.

Local Instance refines_eq_refl A (n : A) : refines Logic.eq n n | 999.
Proof. by rewrite refinesE. Qed.

Local Instance Rseqpoly_edivp_rec :
  refines (Rseqpoly ==> Logic.eq ==> Rseqpoly ==> Rseqpoly ==> Logic.eq ==>
         prod_hrel (prod_hrel Logic.eq Rseqpoly) Rseqpoly)
         (@redivp_rec R) (@div_rec_seqpoly _ _ _ _ _ _).
Proof.
rewrite refinesE=> q sq hsq n m <- {m} p sp hsp r sr hsr m m' <- {m'} /=.
apply refinesP; elim: m => [|m ih] /= in n p sp hsp q sq hsq r sr hsr *;
rewrite -![size_seqpoly _]refines_eq -!sizepE -mul_polyC
        -[_ * 'X^_]/(shiftp (sizep r - sizep q) _).
  case: ifP=> _; rewrite refinesE /prod_hrel //=; do ?split.
    exact: refinesP.
  rewrite /sub_op /sub_seqpoly; exact: refinesP.
case: ifP=> _; first by rewrite refinesE /prod_hrel.
apply: ih=> //.
  exact: refinesP.
rewrite /sub_op /sub_seqpoly; exact: refinesP.
Qed.

Local Instance Rseqpoly_div :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (@rdivp R) div_op.
Proof.
  apply refines_abstr2; rewrite /rdivp unlock=> p sp hsp q sq hsq.
  rewrite [(_ %/ _)%C]/div_seqpoly -sizepE -[(sq == 0)%C]refines_eq;
  case: ifP=> _ /=; rewrite refinesE; exact: refinesP.
Qed.

Local Instance Rseqpoly_mod :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (@rmodp R) mod_op.
Proof.
  apply refines_abstr2; rewrite /rmodp unlock=> p sp hsp q sq hsq.
  rewrite [(_ %% _)%C]/mod_seqpoly -[(sq == 0)%C]refines_eq;
  case: ifP=> _ //; rewrite -sizepE refinesE.
  exact: refinesP.
Qed.

Local Instance Rseqpoly_scal : refines (Rseqpoly ==> Rseqpoly ==> Logic.eq)
  (@rscalp R) (fun p => scal_seqpoly p).
Proof.
  apply refines_abstr2; rewrite /rscalp unlock => p sp hsp q sq hsq.
  rewrite /scal_seqpoly -sizepE -[(sq == 0)%C]refines_eq;
  case: ifP=> _ /=; rewrite refinesE //.
  exact: refinesP.
Qed.

Section seqpoly_param.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, one_of C}.
Context `{opp_of C, add_of C, sub_of C, mul_of C, eq_of C}.
Context `{implem_of R C}.
Context `{!refines rAC 0%R 0%C, !refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) (fun x y => x - y) sub_op}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.

Definition RseqpolyC : {poly R} -> seq C -> Type :=
  (Rseqpoly \o (list_R rAC)).

Global Instance RseqpolyC_cons :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) (@cons_poly R) cons.
Proof. param_comp cons_R. Qed.

Global Instance RseqpolyC_cast :
  refines (rAC ==> RseqpolyC) polyC cast_op.
Proof. param_comp cast_seqpoly_R. Qed.

Global Instance RseqpolyC_0 : refines RseqpolyC 0%R 0%C.
Proof. param_comp seqpoly0_R. Qed.

Global Instance RseqpolyC_1 : refines RseqpolyC 1%R 1%C.
Proof. param_comp seqpoly1_R. Qed.

Global Instance RseqpolyC_opp : refines (RseqpolyC ==> RseqpolyC) -%R -%C.
Proof. param_comp opp_seqpoly_R. Qed.

Global Instance RseqpolyC_add :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) +%R +%C.
Proof. param_comp add_seqpoly_R. Qed.

Global Instance RseqpolyC_sub :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) (fun x y => x - y) sub_op.
Proof. param_comp sub_seqpoly_R. Qed.

Global Instance RseqpolyC_scale :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) *:%R *:%C.
Proof. param_comp scale_seqpoly_R. Qed.

Global Instance RseqpolyC_mul :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) *%R *%C.
Proof. param_comp mul_seqpoly_R. Qed.

Global Instance RseqpolyC_size :
  refines (RseqpolyC ==> nat_R) sizep size_op.
Proof. param_comp size_seqpoly_R. Qed.

Global Instance RseqpolyC_eq :
  refines (RseqpolyC ==> RseqpolyC ==> bool_R) eqtype.eq_op eq_op.
Proof. param_comp eq_seqpoly_R. Qed.

(* This should use nat_R and not eq *)
Global Instance RseqpolyC_shift :
  refines (nat_R ==> RseqpolyC ==> RseqpolyC) shiftp shift_op.
Proof. param_comp shift_seqpoly_R. Qed.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed.

Global Instance RseqpolyC_mulXn p sp n :
  refines RseqpolyC p sp -> refines RseqpolyC (p * 'X^n) (shift_op n sp).
Proof.
  move=> hp; rewrite -[_ * 'X^_]/(shiftp _ _).
  apply: refines_apply.
Qed.

Global Instance RseqpolyC_scaleXn c rc n :
  refines rAC c rc -> refines RseqpolyC (c *: 'X^n) (shift_op n (cast rc)).
Proof.
  move=> hc; rewrite -mul_polyC -[_ * 'X^_]/(shiftp _ _).
  apply: refines_apply.
Qed.

Global Instance RseqpolyC_mulCX p sp :
  refines RseqpolyC p sp -> refines RseqpolyC (p * 'X) (shift_op 1 sp).
Proof.
  move=> hp; rewrite -['X]expr1 -[_ * 'X^_]/(shiftp _ _).
  apply: refines_apply.
Qed.

Global Instance RseqpolyC_scaleCX c rc :
  refines rAC c rc -> refines RseqpolyC (c *: 'X) (shift_op 1 (cast rc)).
Proof.
  move=> hc. rewrite -mul_polyC -['X]expr1 -[_ * 'X^_]/(shiftp _ _).
  apply: refines_apply.
Qed.

(* Uses composable_prod *)
Global Instance RseqpolyC_split :
  refines (nat_R ==> RseqpolyC ==> prod_R RseqpolyC RseqpolyC)
    splitp split_op.
Proof. param_comp split_seqpoly_R. Qed.

Global Instance RseqpolyC_splitn n p sp :
  refines RseqpolyC p sp -> refines (prod_R RseqpolyC RseqpolyC) (splitp n p)
                                    (split_op n sp).
Proof. by move=> hp; apply: refines_apply. Qed.

Definition eq_prod_seqpoly (x y : (seqpoly C * seqpoly C)) :=
  (eq_op x.1 y.1) && (eq_op x.2 y.2).

Global Instance refines_prod_RseqpolyC_eq :
  refines (prod_R RseqpolyC RseqpolyC ==> prod_R RseqpolyC RseqpolyC ==> bool_R)
          eqtype.eq_op eq_prod_seqpoly.
Proof.
  rewrite refinesE=> x x' hx y y' hy.
  rewrite /eqtype.eq_op /eq_prod_seqpoly /=.
  have -> : (x.1 == y.1) = (x'.1 == y'.1)%C.
    apply: refines_eq.
  have -> : (x.2 == y.2) = (x'.2 == y'.2)%C.
    apply: refines_eq.
  exact: bool_Rxx.
Qed.

Global Instance RseqpolyC_lead_coef :
  refines (RseqpolyC ==> rAC) lead_coef lead_coef_op.
Proof.
rewrite /lead_coef_op. (* Why is this necessary? *)
param_comp lead_coef_seqpoly_R.
Qed.

Global Instance RseqpolyC_div :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) (@rdivp R) div_op.
Proof. param_comp div_seqpoly_R. Qed.

Global Instance RseqpolyC_mod :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) (@rmodp R) mod_op.
Proof. param_comp mod_seqpoly_R. Qed.

End seqpoly_param.
End seqpoly_theory.

(* Always simpl Poly. Maybe have refinement instance instead? Is this *)
(* more efficient? *)
Hint Extern 0 (refines _ (Poly _) _) => simpl : typeclass_instances.
Hint Extern 0 (refines _ _ (Poly _)) => simpl : typeclass_instances.

Section testpoly.

From mathcomp Require Import ssrint.
From CoqEAL Require Import binint.

Goal (0 == 0 :> {poly int}).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (0 == (0 : {poly {poly {poly int}}})).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (1 == 1 :> {poly int}).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (1 == (1 : {poly {poly {poly int}}})).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal ((1 + 2%:Z *: 'X + 3%:Z *: 'X^2) + (1 + 2%:Z%:P * 'X + 3%:Z%:P * 'X^2)
      == (1 + 1 + (2%:Z + 2%:Z) *: 'X + (3%:Z + 3%:Z)%:P * 'X^2)).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z; 3%:Z] + Poly [:: 1; 2%:Z; 3%:Z]) ==
      Poly [:: 1 + 1; 2%:Z + 2%:Z; 2%:Z + 4%:Z].
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (- 1 == - (1: {poly {poly int}})).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (- (1 + 2%:Z *: 'X + 3%:Z%:P * 'X^2) == -1 - 2%:Z%:P * 'X - 3%:Z *: 'X^2).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (- Poly [:: 1; 2%:Z; 3%:Z]) == Poly [:: - 1; - 2%:Z; - 3%:Z].
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (1 + 2%:Z *: 'X + 3%:Z *: 'X^2 - (1 + 2%:Z *: 'X + 3%:Z *: 'X^2) == 0).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z; 3%:Z] - Poly [:: 1; 2%:Z; 3%:Z]) == 0.
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X) == 1 + 4%:Z *: 'X + 4%:Z *: 'X^2).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z] * Poly [:: 1; 2%:Z]) == Poly [:: 1; 4%:Z; 4%:Z].
rewrite [_ == _]refines_eq.
by compute.
Abort.

(* (1 + xy) * x = x + x^2y *)
Goal (Poly [:: Poly [:: 1; 0]; 1] * Poly [:: 1; 0]) ==
      Poly [:: Poly [:: 1; 0]; 1 ; 0] :> {poly {poly int}}.
rewrite [_ == _]refines_eq.
by compute.
Abort.

(* (* sizep gives a nat, should one handle it like this? *) *)
(* Local Instance refines_eq_nat  : *)
(*   refines (nat_R ==> nat_R ==> bool_R)%rel eqtype.eq_op eqn. *)
(* Proof. *)
(* rewrite refinesE /eqtype.eq_op /= => m n /nat_R_eq -> m' n' /nat_R_eq ->. *)
(* by case: (eqn _ _). *)
(* Qed. *)

Goal (sizep (1 + 2%:Z *: 'X + 3%:Z *: 'X^2) == 3).
rewrite [sizep _]refines_eq.
by compute.
Abort.

Goal (sizep (Poly [:: 1; 2%:Z; 3%:Z]) == 3%nat).
rewrite [sizep _]refines_eq.
by compute.
Abort.

Goal (splitp 2%nat (Poly [:: 1; 2%:Z; 3%:Z; 4%:Z]) ==
     (Poly [:: 3%:Z; 4%:Z], Poly [:: 1; 2%:Z])).
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

(* Test shiftp *)
Goal (2%:Z *: shiftp 2%nat 1 == Poly [:: 0; 0; 2%:Z]).
rewrite [_ == _]refines_eq.
by compute.
Abort.

End testpoly.
