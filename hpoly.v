(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Refinements.Op. 

(*************************************************************)
(* PART I: Defining datastructures and programming with them *)
(*************************************************************)
Section hpoly.

Variable A pos : Type.

Inductive hpoly := Pc : A -> hpoly
                 | PX : A -> pos -> hpoly -> hpoly.

Section hpoly_op.

Context `{zero A, one A, add A, sub A, opp A, mul A, eq A}.
Context `{one pos, add pos, sub pos, eq pos, lt pos, cast_class nat pos, cast_class pos nat}.

Local Open Scope computable_scope.

Fixpoint normalize (p : hpoly) : hpoly := match p with
  | Pc c => Pc c
  | PX a n p => match normalize p with
    | Pc c => PX a n (Pc c)
    | PX b m q => if (b == 0)%C then PX a (m + n) q else PX a n (PX b m q)
    end
  end.

(* Fixpoint to_seq (p : hpoly A) : seq A := match p with *)
(*   | Pc c => [:: c] *)
(*   | PX a n p => a :: ncons (pred n) 0%C (to_seq p) *)
(*   end. *)

(* TODO: Optimize *)
Fixpoint from_seq (p : seq A) : hpoly := match p with
  | [::] => Pc 0
  | [:: c] => Pc c
  | x :: xs => PX x 1 (from_seq xs)
  end.

(* zero and one *)
Global Instance zero_hpoly : zero hpoly := Pc 0.
Global Instance one_hpoly  : one hpoly  := Pc 1.

Global Instance opp_hpoly : opp hpoly := fix opp_hpoly p := match p with
  | Pc a => Pc (- a)
  | PX a n p => PX (- a) n (opp_hpoly p)
  end.

Fixpoint addXn_const n a q := match q with
  | Pc b      => if n == 0%N then Pc (a + b) else PX b (cast n) (Pc a)
  | PX b m q' => let cn := cast n in
    if n == 0%N then PX (a + b) m q' else 
      if n == cast m    then PX b m (addXn_const 0%N a q') else 
      if (n < cast m)%N then PX b cn (PX a (m - cn) q') 
                        else PX b m (addXn_const (n - cast m)%N a q')
  end.

Arguments addXn_const n a q : simpl never. 

(* Why do I need this? Why isn't simpl never enough?! *)
Definition why n a m q' := addXn_const n a (PX 0 m q').

Fixpoint addXn (n : nat) p q {struct p} := match p, q with
  | Pc a      , q      => addXn_const n a q
  | PX a n' p', Pc b   => if n == 0%N then PX (a + b) n' p' else PX b (cast n) (PX a n' p')
  | PX a n' p', PX b m q' => 
    if n == 0%N then if (n' == m)%C then PX (a + b) n' (addXn 0 p' q') else
                     if n' < m      then PX (a + b) n' (addXn 0 p' (PX 0 (m - n') q'))
                                    else PX (a + b) m (addXn (cast (n' - m)) p' q')
                else addXn (n + cast n') p' (addXn_const 0%N b (why n a m q'))
  end.

Arguments addXn n p q : simpl never. 

(* (* This definition is nicer but Coq doesn't like it *) *)
(* Fixpoint add_hpoly_op p q := match p, q with *)
(*   | Pc a, Pc b     => Pc (a + b) *)
(*   | PX a n p, Pc b => PX (a + b) n p *)
(*   | Pc a, PX b n p => PX (a + b) n p *)
(*   | PX a n p, PX b m q => *)
(*   if (m == n)%C then PX (a + b) n (add_hpoly_op p q) *)
(*                 else if n < m then PX (a + b) n (add_hpoly_op p (PX 0 (m - n) q)) *)
(*                               else PX (a + b) m (add_hpoly_op q (PX 0 (n - m) p)) *)
(*   end. *)

Global Instance add_hpoly : add hpoly := fun p q => addXn 0%N p q.

(* TODO: Prove these operations correct! *)

Fixpoint scale_hpoly a p := match p with
  | Pc b => Pc (a * b)
  | PX b n q => PX (a * b) n (scale_hpoly a q)
  end.

Fixpoint mul_hpoly_op p q := match p, q with
  | Pc a, q => scale_hpoly a q
  | p, Pc b => scale_hpoly b p
  | PX a n p, PX b m q => 
     Pc (a * b) + PX 0 n (scale_hpoly a q) + PX 0 m (scale_hpoly b p) + 
     PX 0 (n + m) (mul_hpoly_op p q)
  end.

Global Instance mul_hpoly : mul hpoly := mul_hpoly_op.

(* TODO: Optimize *)
Definition sub_hpoly_op p q := p + - q.

Global Instance sub_hpoly : sub hpoly := sub_hpoly_op.

Definition shift_hpoly n p := PX 0 n p.

Fixpoint size_hpoly p : nat := match p with
  | Pc a => if (a == 0)%C then 0%N else 1%N
  | PX _ n p' => (cast n + size_hpoly p')%N
  end.

Fixpoint split_hpoly m p : hpoly * hpoly := match p with
  | Pc a => (Pc a, Pc 0)
  | PX a n p' => if (m == 0)%N then (Pc 0,p)
    else let (p1,p2) := split_hpoly (m - cast n)%N p' in (PX a n p1, p2)
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
Variable A : comRingType.

(* REMOVE this once binnat is ok *)
Notation pos := {n : nat | (n > 0)%N}.
Definition posS (n : nat) : pos := exist _ n.+1 isT.

Local Instance zeroA : zero A := 0%R.
Local Instance oneA : one A := 1%R.
Local Instance addA : add A := +%R.
Local Instance oppA : opp A := -%R.
Local Instance subA : sub A := subr.
Local Instance mulA : mul A := *%R.
Local Instance eqA : eq A := eqtype.eq_op.

Local Instance one_pos : one pos := posS 0.
Local Instance add_pos : add pos :=
  fun m n => insubd (posS 0) (val m + val n)%N.
Local Instance sub_pos : sub pos :=
  fun m n => insubd (posS 0) (val m - val n)%N.
Local Instance mul_pos : mul pos :=
  fun m n => insubd (posS 0) (val m * val n)%N.
Local Instance eq_pos : eq pos := eqtype.eq_op.
Local Instance lt_pos : lt pos := fun m n => val m < val n.

Local Instance cast_pos_nat : cast_class pos nat := val.
Local Instance cast_nat_pos : cast_class nat pos := insubd 1%C.

Fixpoint to_poly (p : hpoly A pos) := match p with
  | Pc c => c%:P 
  | PX a n p => to_poly p * 'X^(cast n) + a%:P
  end.

Definition to_hpoly : {poly A} -> hpoly A pos := fun p => from_seq (polyseq p).

Lemma ncons_add : forall m n (a : A) p, ncons (m + n) a p = ncons m a (ncons n a p).
Proof. by elim=> //= m ih n a p; rewrite ih. Qed.

Lemma normalizeK : forall p, to_poly (normalize p) = to_poly p.
Proof.
elim => //= a n p <-; case: (normalize p) => //= b m q.
case: ifP => //= /eqP ->; case: n => [[]] //= n n0.
by rewrite addr0 /cast /cast_pos_nat insubdK /= ?exprD ?mulrA ?addnS.
Qed.

Lemma to_hpolyK : cancel to_hpoly to_poly.
Proof.
elim/poly_ind; rewrite /to_hpoly ?polyseq0 // => p c ih.
rewrite -{1}cons_poly_def polyseq_cons.
have [|pn0] /= := nilP.
  rewrite -polyseq0 => /poly_inj ->; rewrite mul0r add0r.
  apply/poly_inj; rewrite !polyseqC.
  by case c0: (c == 0); rewrite ?polyseq0 // polyseqC c0.
by case: (polyseq p) ih => /= [<-| a l -> //]; rewrite mul0r add0r.
Qed.

Definition Rhpoly : {poly A} -> hpoly A pos -> Prop := fun_hrel to_poly.

(* Program Instance refinement_poly_hpoly : *)
(*   refinement Rhpoly := Refinement to_hpolyK _. *)
(* Next Obligation. by split=> [??[<-]|??<-]. Qed. *)

Lemma refines_hpolyE p q : param Rhpoly p q -> p = to_poly q.
Proof. by rewrite paramE. Qed.

(* zero and one *)
Instance refines_hpoly0 : param Rhpoly 0%R 0%C.
Proof. by rewrite paramE. Qed.

Instance refines_hpoly1 : param Rhpoly 1%R 1%C.
Proof. by rewrite paramE. Qed.

Lemma to_poly_shift : forall n p, to_poly p * 'X^(cast n) = to_poly (PX 0 n p).
Proof. by case; elim => //= n ih h0 hp; rewrite addr0. Qed.

Instance refines_opphpoly : param (Rhpoly ==> Rhpoly) -%R -%C.
Proof.
apply param_abstr => p hp h1.
rewrite [p]refines_hpolyE paramE /Rhpoly /fun_hrel {p h1}.
elim: hp => /= [a|a n p ->]; by rewrite polyC_opp // opprD mulNr.
Qed.
 
Lemma addXn_constE : forall n a q, to_poly (addXn_const n a q) = a%:P * 'X^n + to_poly q.
Proof.
move=> n a q.
elim: q n a.
  move=> a [|n] b /=.
    by rewrite polyC_add expr0 mulr1.
  by rewrite /cast /cast_pos_nat /cast_nat_pos insubdK.
move=> b m q' ih n a /=.
have [->|/eqP m0] /= := eqP; first by rewrite polyC_add expr0 mulr1 addrCA.
have [hn|hnc] /= := eqP; first by rewrite ih expr0 mulr1 -hn mulrDl -addrA.
have [hlt|hleq] /= := ltnP.
rewrite /cast /cast_pos_nat /cast_nat_pos insubdK; last by rewrite -topredE /= lt0n.
rewrite mulrDl -mulrA -exprD addrCA -addrA.
f_equal.
f_equal.
f_equal.
rewrite /sub_op /sub_pos /=.
rewrite ?insubdK.
rewrite subnK //.
by apply/ltnW.
by rewrite -topredE /= lt0n.
by rewrite -topredE /= subn_gt0.
by rewrite -topredE /= lt0n.
by rewrite ih mulrDl -mulrA -exprD subnK // addrA.
Qed.

Lemma addXnE n p q : to_poly (addXn n p q) = to_poly p * 'X^n + to_poly q.
Proof.
elim: p n q.
  move=> a n q.
  simpl.
  by rewrite addXn_constE.
move=> a n' p ih n [b|b m q].
  simpl.
  have [->|/eqP n0] := eqP; first by rewrite expr0 mulr1 /= polyC_add addrA.
  by rewrite /= /cast /cast_pos_nat /cast_nat_pos insubdK // -topredE /= lt0n.
simpl.
have [->|/eqP no] := eqP.
  rewrite expr0 mulr1 /lt_op /lt_pos.
  case: ifP => [/eqP ->|Hneq] /=.
    by rewrite ih expr0 mulr1 mulrDl polyC_add -!addrA [_ + (a%:P + _)]addrCA.
  have [hlt|hleq] /= := ltnP.
    rewrite ih expr0 mulr1 mulrDl /= addr0 -mulrA -exprD polyC_add -!addrA [_ + (a%:P + _)]addrCA.
    rewrite /= /cast /cast_pos_nat /cast_nat_pos insubdK ?subnK //. 
      by apply/ltnW.
    by rewrite -topredE /= subn_gt0.
  rewrite ih mulrDl -mulrA -exprD polyC_add -!addrA [_ + (a%:P + _)]addrCA.
  rewrite /= /cast /cast_pos_nat /cast_nat_pos insubdK ?subnK //. 
  rewrite -topredE /= subn_gt0.
  move: hleq Hneq.
  rewrite leq_eqVlt; case/orP=> // /eqP /val_inj -> /=.
  by rewrite /eq_op /eq_pos eqxx.
rewrite !ih !addXn_constE expr0 mulr1 /= addr0 mulrDl -mulrA -exprD addnC.
rewrite -!addrA.
f_equal.
rewrite addrCA.
f_equal.
by rewrite addrC.
Qed.

Instance refines_addhpoly : param (Rhpoly ==> Rhpoly ==> Rhpoly) +%R +%C.
Proof. 
apply param_abstr2 => p hp h1 q hq h2.
rewrite [p]refines_hpolyE [q]refines_hpolyE paramE /Rhpoly /fun_hrel {p q h1 h2}.
by rewrite /add_op /add_hpoly addXnE expr0 mulr1.
Qed.

End hpoly_theory.

