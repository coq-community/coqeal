(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements binnat.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Refinements.Op. 

(*************************************************************)
(* PART I: Defining datastructures and programming with them *)
(*************************************************************)
Section hpoly.

Variable A : Type.

Inductive hpoly A := Pc : A -> hpoly A
                   | PX : A -> positive -> hpoly A -> hpoly A.

Section hpoly_op.
Context `{zero A, one A, add A, sub A, opp A, mul A, eq A}.

Fixpoint normalize (p : hpoly A) : hpoly A := match p with
  | Pc c => Pc c
  | PX a n p => match normalize p with
    | Pc c => PX a n (Pc c)
    | PX b m q => if (b == 0)%C then PX a (n + m) q else PX a n (PX b m q)
    end
  end.

Fixpoint to_seq (p : hpoly A) : seq A := match p with
  | Pc c => [:: c]
  | PX a n p => a :: ncons (Pos.to_nat n).-1 0%C (to_seq p)
  end.

(* TODO: Optimize *)
Fixpoint from_seq (p : seq A) : hpoly A := match p with
  | [::] => Pc 0%C
  | [:: c] => Pc c
  | x :: xs => PX x 1 (from_seq xs)
  end.

(* zero and one *)
Global Instance zero_hpoly : zero (hpoly A) := Pc 0%C.
Global Instance one_hpoly  : one (hpoly A)  := Pc 1%C.

Global Instance add_hpoly : add (hpoly A) := fun p q => match p, q with
  | Pc a, Pc b => Pc (a + b)%C
  | PX a n p, Pc b => PX (a + b)%C n p
  | Pc a, PX b n p => PX (a + b)%C n p
  | PX a n p, PX b m q => PX (a + b)%C n p (* WHAT TO DO HERE? *)
  end.

(* These things are needed for Karatsuba *)
(* Context `{add polyA, mul polyA, sub polyA}. *)
(* Variable shift_polyA : nat -> polyA -> polyA. *)
(* Variable size_polyA : polyA -> nat. *)
(* Variable splitp_polyA : nat -> polyA -> polyA * polyA. *)

End hpoly_op.
End hpoly.

(***************************)
(* PART II: Develop theory *)
(***************************)
Section hpoly_theory.
Variable A : ringType.

Instance zeroA : zero A := 0%R.
Instance oneA : one A := 1%R.
Instance addA : add A := +%R.
Instance oppA : opp A := -%R.
Instance subA : sub A := subr.
Instance mulA : mul A := *%R.
Instance eqA : eq A := eqtype.eq_op.

Definition hpoly_to_poly : hpoly A -> {poly A} := fun p => Poly (to_seq (normalize p)).
Definition poly_to_hpoly : {poly A} -> hpoly A := fun p => from_seq (polyseq p).

Lemma ncons_add : forall m n (a : A) p, ncons (m + n) a p = ncons m a (ncons n a p).
Proof. by elim=> //= m ih n a p; rewrite ih. Qed.

Lemma normalizeK : forall p, to_seq (normalize p) = to_seq p.
Proof.
elim => //= a n p <-; case: (normalize p) => //= b m q.
case: ifP => //= /eqP ->; rewrite Pos2Nat.inj_add.
case: (Pos.to_nat n) (to_nat_gt0 n) (to_nat_gt0 m) => //= n' _.
by rewrite ncons_add; case: (Pos.to_nat m).
Qed.

Lemma to_seqK : forall p, to_seq (from_seq p) = if p == [::] then [:: 0%C] else p.
Proof. by elim => //= a [] //= b p ->. Qed.

Lemma hpoly_of_polyK : pcancel poly_to_hpoly (some \o hpoly_to_poly).
Proof. 
move=> p; congr Some. 
rewrite /poly_to_hpoly /hpoly_to_poly normalizeK to_seqK -polyseq0.
case: ifP => [/eqP p0 /=|]; last by rewrite polyseqK.
by apply/poly_inj; rewrite p0 polyseqK cons_poly_def mul0r add0r.
Qed.

Definition Rhpoly : {poly A} -> hpoly A -> Prop := fun_hrel hpoly_to_poly.

Program Instance refinement_poly_hpoly :
  refinement Rhpoly := Refinement hpoly_of_polyK _.
Next Obligation. by split=> [??[<-]|??<-]. Qed.

Lemma refines_hpolyE p q : param refines p q -> p = Poly (to_seq q).
Proof. by move<-; rewrite /hpoly_to_poly normalizeK. Qed.

(* zero and one *)
Instance refines_hpoly0 : param refines 0%R 0%C.
Proof. 
rewrite paramE /refines /Rhpoly /fun_hrel /hpoly_to_poly.
by rewrite /zero_op /= cons_poly_def mul0r add0r.
Qed.

Instance refines_hpoly1 : param refines 1%R 1%C.
Proof. 
by rewrite paramE /refines /Rhpoly /fun_hrel /hpoly_to_poly normalizeK /= 
           cons_poly_def mul0r add0r. 
Qed.

Instance refines_addhpoly : param (refines ==> refines ==> refines) +%R +%C.
Proof. 
apply param_abstr2 => p hp h1 q hq h2.
rewrite [p]refines_hpolyE [q]refines_hpolyE.
rewrite paramE /refines /Rhpoly /fun_hrel /hpoly_to_poly normalizeK.
admit.
Qed.

End hpoly_theory.

