(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements.

(******************************************************************************)
(* Lists (seq) is a refinement of SSReflect polynomials (poly)                *) 
(*                                                                            *)
(* Supported operations: 0, 1, +, -, scale, shift                             *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Reserved Notation "\seqpoly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\seqpoly_ ( i  <  n )  E").

Import GRing.Theory.

Section seqpoly.

Variable A : ringType.

Definition seqpoly T := seq T.

Definition seqpoly_def n E : seqpoly A := mkseq E n.
Local Notation "\seqpoly_ ( i < n ) E" := (seqpoly_def n (fun i : nat => E)).

Definition seqpoly_of_poly (p : {poly A}) : seqpoly A := polyseq p.
Definition poly_of_seqpoly (p : seqpoly A) : option {poly A} := Some (Poly p).

Lemma seqpoly_of_polyK : pcancel seqpoly_of_poly poly_of_seqpoly.
Proof. by rewrite /seqpoly_of_poly /poly_of_seqpoly /= => x; rewrite polyseqK. Qed.

Global Program Instance refinement_poly_seqpoly : refinement {poly A} (seqpoly A) := 
  Refinement seqpoly_of_polyK.

(* zero *)
Definition seqpoly_zero : seqpoly A := [::].
Global Instance zero_seqpoly : zero (seqpoly A) := seqpoly_zero.
Global Program Instance refines_poly_0 : refines 0 (0 : seqpoly A)%C.

(* one *)
Definition seqpoly_one : (seqpoly A) := [:: 1].
Global Instance one_seqpoly : one (seqpoly A) := seqpoly_one.

Global Program Instance refines_poly_1 : refines 1 1%C.
Obligation 1.
by congr Some; apply/poly_inj; rewrite polyseq1 polyseq_cons polyseq0 /= polyseq1.
Qed.

(* comp *)
(* Global Program Instance CompSeqpoly `{Comp B} : Comp seqpoly := comp_seqpoly. *)
(* (* I guess compE is needed as well... *) *)
(* Global Program Instance CompMorphSeqpoly `{Comp B, Implem A B} : *)
(*   Morph (implem ==> implem ==> implem) *)
(*         (fun x y => x == y) (fun x y => x == y)%C. *)
(* Obligation 1. admit. Qed. *)

(* lead_coef *) 
(* Definition lead_coef p := p`_(size p).-1. *)
(* Lemma lead_coefE p : lead_coef p = p`_(size p).-1. Proof. by []. Qed. *)

(* nil *)
(* Definition poly_nil := @Polynomial R [::] (oner_neq0 R). *)

(* polyC *)
(* Definition polyC c : {poly R} := insubd poly_nil [:: c]. *)
(* Local Notation "c %:P" := (polyC c). *)

(* Maybe useful lemma about size? *)
(* Lemma refines_size (x : {poly A}) (a : seq A) (xa : refines x a) :  *)
(*   size x <= size a. *)

(* addition *)
Definition seqpoly_add (p q : seqpoly A) : seqpoly A :=
  \seqpoly_(i < maxn (size p) (size q)) (p`_i + q`_i).

Global Instance add_seqpoly : add (seqpoly A) := seqpoly_add.
Global Program Instance refines_poly_add (x y : {poly A}) (a b : seq A)
  (xa : refines x a) (yb : refines y b) : refines (x + y)%R (a + b)%C.
Obligation 1.
congr Some; apply/polyP => i /=.
rewrite -[x](specd_refines x) -[y](specd_refines y) coef_add_poly !coef_Poly.
have [hlt|hleq] := ltnP i (maxn (size a) (size b)); first by rewrite nth_mkseq.
have:= hleq; rewrite geq_max => /andP [ha hb].
by rewrite !nth_default ?addr0 ?size_mkseq.
Qed.

(* The above definition of addition is slow, this should be faster *)
(* Fixpoint add_fast (p q : seqpoly A) : seqpoly A := match p,q with *)
(*   | [::], q => q *)
(*   | p, [::] => p *)
(*   | c :: ps, d :: qs => c + d :: add_fast ps qs *)
(*   end. *)

(* Global Program Instance refines_poly_fastadd (x y : {poly A}) (a b : seq A)  *)
(*   (xa : refines x a) (yb : refines y b) : refines (x + y)%R (fast_add a b). *)
(* Obligation 1. *)


(* negation *)
Definition seqpoly_opp (p : seqpoly A) : seqpoly A := 
  \seqpoly_(i < size p) - p`_i.

Global Instance opp_seqpoly : opp (seqpoly A) := seqpoly_opp.
Global Program Instance refines_poly_opp (x : {poly A}) (a : seq A) 
  (xa : refines x a) : refines (- x)%R (- a)%C.
Obligation 1.
congr Some; apply/polyP => i /=.
rewrite -[x](specd_refines x) coef_opp_poly !coef_Poly.
have [hlt|hleq] := ltnP i (size a); first by rewrite nth_mkseq.
by rewrite !nth_default ?oppr0 ?size_mkseq.
Qed.

(* scaling *)
Definition seqpoly_scale a (p : seqpoly A) := \seqpoly_(i < size p) (a * p`_i).

Local Notation "*:%C" := (@seqpoly_scale _ _).
Local Notation "a *: v" := (seqpoly_scale a v) : computable_scope.

(* That we must have x in both places is a bit wierd? *)
Global Program Instance refines_seqpoly_scale (x : A) (p : {poly A}) (s : seqpoly A)
  (ps : refines p s) : refines (x *: p)%R (x *: s)%C.
Obligation 1.
congr Some; apply/polyP => i /=.
rewrite -[p](specd_refines p) coefZ !coef_Poly.
have [hlt|hleq] := ltnP i (size s); first by rewrite nth_mkseq.
by rewrite !nth_default ?mulr0 ?size_mkseq.
Qed.

(* shifting = * 'X^n *)
Definition shift n p : seqpoly A := ncons n 0 p.

Global Program Instance refines_seqpoly_shift n (p : {poly A}) (s : seqpoly A)
  (ps : refines p s) : refines (p * 'X^n)%R (shift n s)%C.
Obligation 1.
congr Some; apply/polyP => i /=.
by rewrite -[p](specd_refines p) /shift coefMXn !coef_Poly nth_ncons.
Qed.

(* multiplication *) 
(* Definition seqpoly_mul p q := *)
(*   \seqpoly_(i < (size p + size q).-1) (\sum_(j < i.+1) p`_j * q`_(i - j)). *)

(* Fixpoint seqpoly_mul p q : seqpoly A := match p,q with *)
(*   | [::], _ => 0%C *)
(*   | _, [::] => 0%C *)
(*   | x :: xs,_ => (x *: q + seqpoly_mul xs (shift 1 q))%C *)
(*   end. *)

(* Global Program Instance mul_seqpoly : mul (seqpoly A) := seqpoly_mul. *)

(* Global Program Instance refines_poly_mul (x y : {poly A}) (a b : seq A)  *)
(*   (xa : refines x a) (yb : refines y b) : refines (x * y)%R (a * b)%C. *)
(* Obligation 1. *)
(* congr Some; apply/polyP => i /=. *)
(* rewrite -[x](specd_refines x) -[y](specd_refines y) coef_mul_poly !coef_Poly. *)
(* admit. *)
(* (* have [hlt|hleq] := ltnP i (maxn (size a) (size b)); first by rewrite nth_mkseq. *) *)
(* (* have:= hleq; rewrite geq_max => /andP [ha hb]. *) *)
(* (* by rewrite !nth_default ?addr0 ?size_mkseq. *) *)
(* Qed. *)

(* Lemma mul_seqr0 : forall p, mul_seq p [::] = [::]. *)
(* Proof. by case. Qed. *)

(* Lemma mul_seqE : {morph trans : p q / p * q >-> mul_seq p q}. *)
(* Proof. *)
(* elim/poly_ind=> [|p c IH] q; first by rewrite mul0r zeroE /zero. *)
(* case q0: (q == 0); first by rewrite (eqP q0) mulr0 zeroE /zero mul_seqr0. *)
(* rewrite !trans_poly_def -!cons_poly_def polyseq_cons. *)
(* elim/poly_ind: q q0=> [|q d _ /eqP /eqP q0]; first by rewrite eqxx. *)
(* rewrite /nilp. *)
(* case sp: (size p == 0%N) => /=. *)
(*   rewrite size_poly_eq0 in sp; rewrite (eqP sp) polyseqC. *)
(*   case c0: (c == 0). *)
(*     by rewrite (eqP c0) cons_poly_def mul0r add0r mul0r polyseq0. *)
(*   rewrite /= -scale_seqE -cons_poly_def polyseq_cons cons_poly_def. *)
(*   case: ifP=> [sq|]. *)
(*     by rewrite scale_polyE -trans_poly0 -add_seqE addr0 mul0r add0r. *)
(*   rewrite size_poly_neq0 => /eqP; rewrite -polyseq0 => /poly_inj ->. *)
(*   rewrite polyseqC. *)
(*   case d0: (d == 0). *)
(*     by rewrite (eqP d0) !cons_poly_def mul0r !add0r mulr0 /= polyseq0. *)
(*   by rewrite !cons_poly_def scale_polyE mul0r !add0r add_seqr0. *)
(* rewrite -shiftE expr1 -IH. *)
(* rewrite -scale_seqE -cons_poly_def polyseq_cons /=. *)
(* case: ifP => /= sq0. *)
(*   by rewrite !cons_poly_def scale_polyE -add_seqE !mulrDl -!mulrA addrC *)
(*              !mulrDr [d%:P * 'X]mulrC ['X * (q * 'X)]mulrCA. *)
(* rewrite polyseqC. *)
(* move: sq0. *)
(* rewrite /nilp size_poly_eq0 => /eqP ->. *)
(* case d0: (d == 0) => /=. *)
(*   by rewrite (eqP d0) !cons_poly_def mul0r addr0 mulr0 polyseq0. *)
(* by rewrite scale_polyE -add_seqE !cons_poly_def mul0r add0r addrC mulrDl *)
(*            [d%:P * _]mulrC mulrA. *)
(* Qed. *)

(* X *)
Definition seqpolyX : seqpoly A := [:: 0; 1].
Local Notation "'X" := seqpolyX : computable_scope.

(* monic *)
(* Definition monic := [qualify p | lead_coef p == 1]. *)

(* horner evaluation *)
Definition horner_seqpoly (p : seqpoly A) x := horner_rec p x.
Local Notation "p .[ x ]" := (horner_seqpoly p x) : computable_scope.

(* single derivative *)
(* Definition deriv p := \poly_(i < (size p).-1) (p`_i.+1 *+ i.+1). *)
(* Local Notation "a ^` ()" := (deriv a). *)

(* iterated derivative *)
(* Definition derivn n p := iter n deriv p. *)
(* Local Notation "a ^` ( n )" := (derivn n a) : ring_scope. *)

(* map_poly = map *)
(* Definition map_poly (p : {poly aR}) := \poly_(i < size p) f p`_i. *)

(* unit *)
(* Definition poly_unit : pred {poly R} := *)
(*   fun p => (size p == 1%N) && (p`_0 \in GRing.unit). *)

(* inverse *)
(* Definition poly_inv p := if p \in poly_unit then (p`_0)^-1%:P else p. *)

End seqpoly.

(* This does not work as seqpoly is not using parametricity yet! *)
(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0 + 0)%C : seqpoly Z. *)
(* Eval compute in (1 + 1)%C : seqpoly Z. *)
(* Eval compute in 1%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1)%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1 + 1 + 1 + 1)%C : *)
(*   seqpoly (seqpoly (seqpoly (seqpoly (seqpoly Z)))). *)