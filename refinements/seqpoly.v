From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

From CoqEAL Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op.

Local Open Scope ring_scope.
Local Open Scope rel.

(* Specific classes for polynomials *)
Section classes.

Class shift_of polyA := shift_op : nat -> polyA -> polyA.
Class split_of polyA := split_op : nat -> polyA -> polyA * polyA.
Class size_of polyA := size_op : polyA -> nat.
Class lead_coef_of A polyA := lead_coef_op : polyA -> A.

End classes.

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
  fun n p => (take n p,drop n p).

Global Instance lead_coef_seqpoly : lead_coef_of A seqpoly :=
  fun p => nth 0 p (size_seqpoly p).-1.

(* pseudo-division *)
Definition div_rec_seqpoly (q : seqpoly) :=
  let sq := size_op q in
  let cq := cast_op (lead_coef_op q) in
  fix loop (k : nat) (qq r : seqpoly) (n : nat) {struct n} :=
    if (size_op r < sq)%nat then (k, qq, r) else
    let m := shift_seqpoly (size_op r - sq)%nat
                           (cast_op (lead_coef_op r)) in
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

(* TODO: Add this *)
(* Definition scalp_seqpoly p q := *)
(*   (if (q == 0)%C then (0%N, 0%C, p) *)
(*                  else edivp_rec_seqpoly q 0 0%C p (size_seqpoly p)).1.1. *)

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

Section seqpoly_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oneR  : one_of R  := 1%R.
Local Instance addR  : add_of R  := +%R.
Local Instance subR  : sub_of R  := fun x y => x - y.
Local Instance mulR  : mul_of R  := *%R.
Local Instance oppR  : opp_of R  := -%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.

(* Lemma seqpoly_of_polyK : pcancel (@polyseq R) (some \o Poly). *)
(* Proof. by move=> p /=; rewrite polyseqK. Qed. *)

Definition splitp : nat -> {poly R} -> {poly R} * {poly R} :=
  fun n p => (rdivp p 'X^n, rmodp p 'X^n).

Definition shiftp n (p : {poly R}) := p * 'X^n.

Definition Rseqpoly : {poly R} -> seqpoly R -> Type := fun p sp => p = Poly sp.

Local Open Scope rel_scope.

Instance Rseqpoly_cons :
  refines (eq ==> Rseqpoly ==> Rseqpoly) (@cons_poly R) cons.
Proof.
rewrite !refinesE => x y -> p sp ->.
exact: poly_inj.
Qed.

Instance Rseqpoly_cast : refines (eq ==> Rseqpoly) polyC cast_op.
Proof.
rewrite !refinesE=> x y ->.
by apply: poly_inj; rewrite polyseq_cons polyseq0.
Qed.

Instance Rseqpoly_0 : refines Rseqpoly 0%R 0%C.
Proof. by rewrite refinesE. Qed.

Instance Rseqpoly_1 : refines Rseqpoly 1%R 1%C.
Proof. by rewrite refinesE /Rseqpoly /= cons_poly_def mul0r add0r. Qed.

Instance Rseqpoly_opp : refines (Rseqpoly ==> Rseqpoly) -%R -%C.
Proof.
rewrite refinesE /Rseqpoly => p sp -> {p}.
apply/polyP => i /=; rewrite coef_opp_poly !coef_Poly.
have [hlt|hleq] := ltnP i (size sp); first by rewrite (nth_map 0%C).
by rewrite !nth_default ?oppr0 ?size_mkseq ?size_map.
Qed.

Instance Rseqpoly_add : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) +%R +%C.
Proof.
rewrite refinesE /Rseqpoly => p sp -> q sq -> {p q}.
elim: sp sq=> [[] /= *|a p ih [|b q]] /=; do ?rewrite ?add0r ?addr0 //.
by rewrite !cons_poly_def -ih addrAC addrA -mulrDl raddfD /= -!addrA [_ + a%:P]addrC.
Qed.

Lemma opp_map (p : seq R) : - Poly p = Poly (List.map -%C p).
Proof.
  elim: p=> [|a p ihp] /=; first by rewrite oppr0.
  by rewrite !cons_poly_def opprD polyC_opp -mulNr ihp.
Qed.  

Instance Rseqpoly_sub : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (fun x y => x - y) sub_op.
Proof.
  rewrite refinesE /Rseqpoly=> _ sp -> _ sq ->.
  elim: sp sq=> [[|b q]|a p ihp [|b q]] /=; rewrite ?add0r ?oppr0 ?addr0 //.
    by rewrite !cons_poly_def opprD polyC_opp /opp_seqpoly -mulNr opp_map.
  by rewrite !cons_poly_def -ihp polyC_add polyC_opp opprD addrAC addrA addrAC addrA mulrDl mulNr.
Qed.

(* scaling *)

Lemma scale_map (a : R) (p : seq R) : a *: Poly p = Poly (scale_seqpoly a p).
Proof.
  elim: p=> [|b p ihp] /=; first by rewrite scaler0.
  by rewrite !cons_poly_def scalerDr scalerAl polyC_mul mul_polyC ihp.
Qed.

Instance Rseqpoly_scale : refines (eq ==> Rseqpoly ==> Rseqpoly) *:%R *:%C.
Proof.
  rewrite refinesE /Rseqpoly=> _ a -> _ sp ->.
  elim: sp=> [|b p ihp] /=; first by rewrite scaler0.
  by rewrite !cons_poly_def scalerDr scalerAl polyC_mul mul_polyC scale_map.
Qed.

Lemma consSeqpoly (p : seq R) (a : R) : Poly (a::p)%C = a%:P + Poly p * 'X.
Proof.
  elim: p=> [|b p ihp] /=; first by rewrite cons_poly_def mul0r addrC.
  by rewrite !cons_poly_def addrC [Y in (Y * 'X)]addrC.
Qed.

Lemma addSeqpoly (p q : seq R) : Poly (p + q)%C = Poly p + Poly q.
Proof.
  elim: p q=> [q|a p ihp [|b q]] /=;
    first by rewrite [((_ + _)%C)]/add_seqpoly /add_seqpoly_fun add0r.
    by rewrite cons_poly_def addr0.
  by rewrite !cons_poly_def ihp polyC_add [in RHS]addrACA -[in RHS]mulrDl.
Qed.

(* multiplication *)
Instance Rseqpoly_mul : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) *%R *%C.
Proof.
  rewrite refinesE /Rseqpoly=> _ sp -> _ sq ->.
  elim: sp => [|a p ihp] /=; first by rewrite mul0r.
  rewrite cons_poly_def mulrDl commr_polyX -mulrA mul_polyC.  
  by rewrite addSeqpoly consSeqpoly /= polyC0 add0r -scale_map addrC commr_polyX ihp.
Qed.

(* This definition hides the coercion which makes it possible for proof search
   to find Rseqpoly_seqpoly_size *)
Definition sizep : {poly R} -> nat := size.
Lemma sizepE s : sizep s = size s. Proof. by []. Qed.

Instance Rseqpoly_size :
  refines (Rseqpoly ==> eq) sizep size_op.
Proof.
  rewrite refinesE => _ sp ->; rewrite sizepE /size_op.
  elim: sp=> [|a p ihp]/=; first by rewrite size_poly0.
  rewrite size_cons_poly /nilp ihp eqnE Bool.andb_if; simpC.
  case: (a == 0)=> /=.
    by [].
  case hp: (size_seqpoly p == 0%C).
    by apply/eqP; rewrite -addn1 -[(1%N)]add0n eqn_add2r hp.
  by [].
Qed.

Instance Rseqpoly_eq :
  refines (Rseqpoly ==> Rseqpoly ==> Logic.eq) eqtype.eq_op eq_op.
Proof.
  rewrite refinesE /eq_op /eq_seqpoly=> _ sp -> _ sq ->.
  apply/eqP/allP=> [hsq x|hsq].
Admitted.

(* These can be done with eq instead of nat_R *)
Instance Rseqpoly_shift :
  refines (eq ==> Rseqpoly ==> Rseqpoly) shiftp shift_op.
Admitted.

Instance Rseqpoly_split :
  refines (eq ==> Rseqpoly ==> prod_hrel Rseqpoly Rseqpoly)
          splitp split_op.
Admitted.

Instance Rseqpoly_lead_coef :
  refines (Rseqpoly ==> eq) lead_coef lead_coef_op.
Admitted.

Instance Rseqpoly_div :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (@rdivp R) div_op.
Admitted.

Instance Rseqpoly_mod :
  refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (@rmodp R) mod_op.
Admitted.

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

(* Lower priority to make karatsuba default instance *)
Global Instance RseqpolyC_mul :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) *%R *%C | 1.
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

(* Uses composable_prod *)
Global Instance RseqpolyC_split :
  refines (nat_R ==> RseqpolyC ==> prod_R RseqpolyC RseqpolyC)
    splitp split_op.
Proof. param_comp split_seqpoly_R. Qed.

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

(* Always simpl Poly. Maybe have refinement instance instead? Is this
more efficient? *)
Hint Extern 0 (refines _ (Poly _) _) => simpl : typeclass_instances.
Hint Extern 0 (refines _ _ (Poly _)) => simpl : typeclass_instances.

Section testpoly.

From mathcomp Require Import ssrint.
From CoqEAL Require Import binint.

Goal (0 == (0 : {poly {poly {poly int}}})).
rewrite [_ == _]refines_eq.
do ?rewrite /zero_op /seqpoly0.
by compute.
Abort.

Goal (1 == (1 : {poly {poly {poly int}}})).
rewrite [_ == _]refines_eq.
do ?rewrite /one_op /seqpoly1.
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

Goal (- Poly [:: 1; 2%:Z; 3%:Z]) == Poly [:: - 1; - 2%:Z; - 3%:Z].
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z; 3%:Z] - Poly [:: 1; 2%:Z; 3%:Z]) == 0.
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

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed.

(* sizep gives a nat, should one handle it like this? *)
Local Instance refines_eq_nat  :
  refines (nat_R ==> nat_R ==> bool_R)%rel eqtype.eq_op eqn.
Proof.
rewrite refinesE /eqtype.eq_op /= => m n /nat_R_eq -> m' n' /nat_R_eq ->.
case: (eqn _ _); [ exact: true_R | exact: false_R ].
Qed.

Goal (sizep (Poly [:: 1; 2%:Z; 3%:Z]) == 3%nat).
rewrite [_ == _]refines_eq.
by compute.
Abort.

(* This is not working... *)
(* Goal (split_polyR 2%nat (Poly [:: 1; 2%:Z; 3%:Z; 4%:Z]) == *)
(*      (Poly [:: 1; 2%:Z],Poly [:: 3%:Z; 4%:Z])). *)
(* rewrite /= [_ == _]refines_eq. *)
(* by compute. *)
(* Abort. *)

(* Test shiftp *)
Goal (2%:Z *: shiftp 2%nat 1 == Poly [:: 0; 0; 2%:Z]).
rewrite [_ == _]refines_eq.
by compute.
Abort.

End testpoly.
