Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op.

Local Open Scope ring_scope.
Local Open Scope rel.

Section seqpoly_op.

Local Open Scope computable_scope.

Variable T : Type.

Definition seqpoly := seq T.

Context `{zero_of T, one_of T, add_of T, opp_of T, mul_of T, eq_of T}.

Global Instance seqpoly0 : zero_of seqpoly := [::].
Global Instance seqpoly1 : one_of seqpoly := [:: 1].
Global Instance seqpoly_opp : opp_of seqpoly := List.map -%C.

Fixpoint add_seqpoly (p q : seqpoly) : seqpoly := match p,q with
  | [::], q => q
  | p, [::] => p
  | a :: p', b :: q' => a + b :: add_seqpoly p' q'
  end.

Global Instance seqpoly_add : add_of seqpoly := add_seqpoly.
Global Instance seqpoly_sub : sub_of seqpoly := fun x y => (x + - y)%C.

Global Instance seqpoly_scale : scale_of T seqpoly := fun a => map ( *%C a).

(* 0%C :: aux p = shift 1 (aux p) *)
Global Instance seqpoly_mul : mul_of seqpoly := fun p q =>
  let fix aux p :=
      if p is a :: p then (a *: q + (0%C :: aux p))%C else 0
  in aux p.

Global Instance size_seqpoly : size_of seqpoly :=
  let fix aux p :=
      if p is a :: p then
        let sp := aux p in
        if (eqn sp 0)%nat then ~~ (a == 0)%C : nat else sp.+1
      else 0%nat in aux.

Global Instance seqpoly_eq : eq_of seqpoly := fun p q =>
  all (fun x => x == 0)%C (p - q)%C.

End seqpoly_op.

Parametricity seqpoly0.
Parametricity seqpoly1.
Parametricity seqpoly_opp.
Parametricity seqpoly_add.
Parametricity seqpoly_sub.
Parametricity seqpoly_scale.
Parametricity seqpoly_mul.
Parametricity size_seqpoly.
Parametricity seqpoly_eq.

Section seqpoly_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oneR  : one_of R  := 1%R.
Local Instance addR  : add_of R  := +%R.
Local Instance mulR  : mul_of R  := *%R.
Local Instance oppR  : opp_of R  := -%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.

(* Lemma seqpoly_of_polyK : pcancel (@polyseq R) (some \o Poly). *)
(* Proof. by move=> p /=; rewrite polyseqK. Qed. *)

Definition Rseqpoly : {poly R} -> seqpoly R -> Type := fun p sp => p = Poly sp.

Local Open Scope rel_scope.

Instance Rseqpoly_cons : refines (Logic.eq ==> Rseqpoly ==> Rseqpoly) (@cons_poly R) cons.
Proof.
rewrite !refinesE => x y -> p sp hp.
apply/polyP => i /=.
rewrite cons_poly_def.
admit.
Qed.

Instance Rseqpoly_0 : refines Rseqpoly 0%R 0%C.
Proof. by rewrite refinesE. Qed.

Instance Rseqpoly_1 : refines Rseqpoly 1%R 1%C.
Proof. by rewrite refinesE /Rseqpoly /= cons_poly_def mul0r add0r. Qed.

Instance Rseqpoly_opp : refines (Rseqpoly ==> Rseqpoly) -%R -%C.
Proof.
rewrite refinesE /Rseqpoly => p sp -> {p}.
apply/polyP => i /=; rewrite /opp_op /seqpoly_opp /=.
rewrite coef_opp_poly !coef_Poly.
have [hlt|hleq] := ltnP i (size sp); first by rewrite (nth_map 0%C).
by rewrite !nth_default ?oppr0 ?size_mkseq ?size_map.
Qed.

Instance Rseqpoly_add : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) +%R +%C.
Proof.
rewrite refinesE /Rseqpoly => p sp -> q sq -> {p q}.
elim: sp sq=> [[] /= *|a p ih [|b q]] /=; do ?rewrite ?add0r ?addr0 //.
by rewrite !cons_poly_def -ih addrAC addrA -mulrDl raddfD /= -!addrA [_ + a%:P]addrC.
Qed.

Instance Rseqpoly_sub : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (fun x y => x - y) sub_op.
Admitted.

(* scaling *)
Instance Rseqpoly_scale : refines (Logic.eq ==> Rseqpoly ==> Rseqpoly) *:%R *:%C.
Admitted.

(* multiplication *)
Instance Rseqpoly_mul : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) *%R *%C.
Admitted.

(* This definition hides the coercion which makes it possible for proof search
   to find Rseqpoly_seqpoly_size *)
Definition sizep : {poly R} -> nat := size.
Lemma sizepE s : sizep s = size s. Proof. by []. Qed.

Instance Rseqpoly_size :
  refines (Rseqpoly ==> Logic.eq) sizep size_op.
Admitted.

Instance Rseqpoly_eq : refines (Rseqpoly ==> Rseqpoly ==> bool_R) eqtype.eq_op eq_op.
Admitted.

Section seqpoly_param.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, one_of C, opp_of C, add_of C, mul_of C, eq_of C}.
Context `{implem_of R C}.
Context `{!refines rAC 0%R 0%C, !refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.

Definition RseqpolyC : {poly R} -> seq C -> Type :=
  (Rseqpoly \o (list_R rAC)).

Global Instance RseqpolyC_cons :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) (@cons_poly R) cons.
Proof. param_comp cons_R. Qed.

Global Instance RseqpolyC_0 : refines RseqpolyC 0%R 0%C.
Proof. param_comp seqpoly0_R. Qed.

Global Instance RseqpolyC_1 : refines RseqpolyC 1%R 1%C.
Proof. param_comp seqpoly1_R. Qed.

Global Instance RseqpolyC_opp : refines (RseqpolyC ==> RseqpolyC) -%R -%C.
Proof. param_comp seqpoly_opp_R. Qed.

Global Instance RseqpolyC_add : 
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) +%R +%C.
Proof. param_comp seqpoly_add_R. Qed.

Global Instance RseqpolyC_sub : 
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) (fun x y => x - y) sub_op.
Proof. param_comp seqpoly_sub_R. Qed.

Global Instance RseqpolyC_scale :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) *:%R *:%C.
Proof. param_comp seqpoly_scale_R. Qed.

(* Lower priority to make karatsuba default instance *)
Global Instance RseqpolyC_mul :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) *%R *%C | 1.
Proof. param_comp seqpoly_mul_R. Qed.

Global Instance RseqpolyC_size :
  refines (RseqpolyC ==> nat_R) sizep size_op.
Proof. param_comp size_seqpoly_R. Qed.

Global Instance RseqpolyC_eq :
  refines (RseqpolyC ==> RseqpolyC ==> bool_R) eqtype.eq_op eq_op.
Proof. param_comp seqpoly_eq_R. Qed.

End seqpoly_param.
End seqpoly_theory.

Section testpoly.

Require Import binint ssrint.

Goal (1 == (1 : {poly {poly {poly int}}})).
rewrite [_ == _]refines_eq.
do ?rewrite /one_op /seqpoly1.
by compute.
Abort.
 
Goal (Poly [:: 1; 2%:Z; 3%:Z] + Poly [:: 1; 2%:Z; 3%:Z]) == Poly [:: 1 + 1; 2%:Z + 2%:Z; 2%:Z + 4%:Z].
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Goal (- 1 == - (1: {poly {poly int}})).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (- Poly [:: 1; 2%:Z; 3%:Z]) == Poly [:: - 1; - 2%:Z; - 3%:Z].
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z; 3%:Z] - Poly [:: 1; 2%:Z; 3%:Z]) == 0.
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z] * Poly [:: 1; 2%:Z]) == Poly [:: 1; 4%:Z; 4%:Z].
rewrite /= [_ == _]refines_eq.
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
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

(* This is not working... *)
(* Goal (split_polyR 2%nat (Poly [:: 1; 2%:Z; 3%:Z; 4%:Z]) == *)
(*      (Poly [:: 1; 2%:Z],Poly [:: 3%:Z; 4%:Z])). *)
(* rewrite /= [_ == _]refines_eq. *)
(* by compute. *)
(* Abort. *)

End testpoly.
