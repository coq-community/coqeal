(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements pos.

(******************************************************************************)
(** This file implements sparse polynomials in sparse Horner normal form.     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Refinements.Op. 

(******************************************************************************)
(** PART I: Defining generic datastructures and programming with them         *)
(******************************************************************************)
Section hpoly.

Context {A N pos : Type}.

Inductive hpoly := Pc : A -> hpoly
                 | PX : A -> pos -> hpoly -> hpoly.

Section hpoly_op.

Context `{zero A, one A, add A, sub A, opp A, mul A, eq A}.
Context `{one pos, add pos, sub pos, eq pos, lt pos}.
Context `{zero N, eq N, lt N, add N, sub N}.
Context `{cast_class N pos, cast_class pos N, cast_class pos nat}.

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

Global Instance opp_hpoly : opp hpoly := fix f p := match p with
  | Pc a => Pc (- a)
  | PX a n p => PX (- a) n (f p)
  end.

Fixpoint addXn_const n a q := match q with
  | Pc b      => if (n == 0)%C then Pc (a + b) else PX b (cast n) (Pc a)
  | PX b m q' => let cn := cast n in
    if (n == 0)%C then PX (a + b) m q' else 
      if (n == cast m)%C    then PX b m (addXn_const 0 a q') else 
      if n < cast m then PX b cn (PX a (m - cn) q') 
                    else PX b m (addXn_const (n - cast m)%C a q')
  end.

Fixpoint addXn (n : N) p q {struct p} := match p, q with
  | Pc a      , q      => addXn_const n a q
  | PX a n' p', Pc b   => if (n == 0)%C then PX (a + b) n' p' 
                                        else PX b (cast n) (PX a n' p')
  | PX a n' p', PX b m q' => 
    if (n == 0)%C then 
      if (n' == m)%C then PX (a + b) n' (addXn 0 p' q') else
      if n' < m      then PX (a + b) n' (addXn 0 p' (PX 0 (m - n') q'))
                     else PX (a + b) m (addXn (cast (n' - m)) p' q')
    else addXn (n + cast n') p' (addXn_const 0 b (addXn_const n a (PX 0 m q')))
  end.

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

Global Instance add_hpoly : add hpoly := addXn 0.

Global Instance scale_hpoly : scale A hpoly := fix f a p := match p with
  | Pc b => Pc (a * b)
  | PX b n q => PX (a * b) n (f a q)
  end.

Global Instance mul_hpoly : mul hpoly := fix f p q := match p, q with
  | Pc a, q => a *: q
  | p, Pc b => b *: p
  | PX a n p, PX b m q => 
     PX 0 (n + m) (f p q) + PX 0 m (a *: q) + (PX 0 n (b *: p) + Pc (a * b))
  end.

(* TODO: Optimize *)
Global Instance sub_hpoly : sub hpoly := fun p q => p + - q.

Fixpoint eq0_hpoly (p : hpoly) : bool :=
  match p with
    | Pc a      => (a == 0)%C
    | PX a n p' => (a == 0)%C && (eq0_hpoly p')
  end.

Global Instance eq_hpoly : eq hpoly := fun p q => eq0_hpoly (p - q).

(* Alternative definition, should be used with normalize: *)
(* Fixpoint eq_hpoly_op p q {struct p} := match p, q with *)
(*   | Pc a, Pc b => (a == b)%C *)
(*   | PX a n p', PX b m q' => (a == b)%C && (cast n == cast m) && (eq_hpoly_op p' q') *)
(*   | _, _ => false *)
(*   end. *)

(* TODO: Prove these operations correct! *)
Definition shift_hpoly n p := PX 0 n p.

Fixpoint size_hpoly p := match p with
  | Pc a => if (a == 0)%C then 0%N else 1%N
  | PX a n p' => if (p == 0)%C && (a == 0)%C 
                 then 0%N else (cast n + size_hpoly p').+1
  end.

Fixpoint split_hpoly m p : hpoly * hpoly := match p with
  | Pc a => (Pc a, Pc 0)
  | PX a n p' => if (m == 0)%N then (Pc 0,p)
    else let (p1,p2) := split_hpoly (m - cast n)%N p' in (PX a n p1, p2)
  end.

End hpoly_op.
End hpoly.


(******************************************************************************)
(** PART II: Proving correctness properties of the previously defined objects *)
(******************************************************************************)
Section hpoly_theory.

Variable A : comRingType.

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
Local Instance eq_pos  : eq pos := eqtype.eq_op.
Local Instance lt_pos  : lt pos  := fun m n => val m < val n.

Local Instance zero_nat : zero nat := 0%N.
Local Instance eq_nat   : eq nat   := fun m n => m == n.
Local Instance lt_nat   : lt nat   := ltn.
Local Instance add_nat  : add nat  := addn.
Local Instance sub_nat  : sub nat  := subn.

Local Instance cast_pos_nat : cast_class pos nat := val.
Local Instance cast_nat_pos : cast_class nat pos := insubd 1%C.

Fixpoint to_poly (p : @hpoly A pos) := match p with
  | Pc c => c%:P 
  | PX a n p => to_poly p * 'X^(cast n) + a%:P
  end.

(* Global Instance spec_hpoly : spec_of (hpoly A pos) {poly A} := to_poly. *)

Definition to_hpoly : {poly A} -> @hpoly A pos := fun p => from_seq (polyseq p).

Lemma ncons_add : forall m n (a : A) p, 
  ncons (m + n) a p = ncons m a (ncons n a p).
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

Definition Rhpoly : {poly A} -> @hpoly A pos -> Prop := fun_hrel to_poly.

(* This is OK here, but not everywhere *)
Local Instance param_eqA (x : A) : param Logic.eq x x.
Proof. by rewrite paramE. Qed.

Lemma RhpolyE p q : param Rhpoly p q -> p = to_poly q.
Proof. by rewrite paramE. Qed.

Instance refines_spec_hpoly_r x : param Rhpoly (to_poly x) x | 10000.
Proof. by rewrite !paramE; case: x. Qed.

Fact normalize_lock : unit. Proof. exact tt. Qed.
Definition normalize_id := locked_with normalize_lock (@id {poly A}).
Lemma normalize_idE p : normalize_id p = p.
Proof. by rewrite /normalize_id unlock. Qed.

Instance refines_normalize : param (Rhpoly ==> Rhpoly) normalize_id normalize.
Proof.
rewrite paramE => p hp rp.
by rewrite /Rhpoly /fun_hrel normalizeK normalize_idE.
Qed.

(* TODO: Finish this proof! *)
(* For now, do it for comRingType *)
(* Lemma size_MXnaddC (R : comRingType) (p : {poly R}) (c : R) n : *)
(*    size (p * 'X^n + c%:P) = if (p == 0) && (c == 0) then 0%N else (n + size p).+1. *)
(* Proof. *)
(* admit. *)
(* Qed. *)

(* Instance refines_hpoly_eq0 : param (Rhpoly ==> Logic.eq)  *)
(*   (fun p => p == 0) (eq0_hpoly)%C. *)
(* Proof. *)
(* rewrite paramE => p hp rp; rewrite [p]RhpolyE {p rp}. *)
(* elim: hp => [a|a n p ih] /=; first by rewrite polyC_eq0. *)
(* by rewrite -size_poly_eq0 -ih size_MXnaddC andbC; case: ifP. *)
(* Qed. *)

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
rewrite [p]RhpolyE paramE /Rhpoly /fun_hrel {p h1}.
elim: hp => /= [a|a n p ->]; by rewrite polyC_opp // opprD mulNr.
Qed.

Lemma addXn_constE n a q : to_poly (addXn_const n a q) = a%:P * 'X^n + to_poly q.
Proof.
elim: q n => [b [|n]|b m q' ih n] /=; simpC; first by rewrite polyC_add expr0 mulr1.
  by rewrite /cast /cast_pos_nat insubdK.
case: eqP => [->|/eqP n0] /=; first by rewrite polyC_add expr0 mulr1 addrCA.
case: eqP => [hn|hnc] /=; first by rewrite ih expr0 mulr1 -hn mulrDl -addrA.
have [hlt|hleq] /= := ltnP; rewrite /cast /cast_nat_pos /cast_pos_nat.
  rewrite insubdK -?topredE /= ?lt0n // mulrDl -mulrA -exprD addrCA -addrA.
  by rewrite ?insubdK -?topredE /= ?subn_gt0 ?lt0n ?subnK // ltnW. 
by rewrite ih mulrDl -mulrA -exprD subnK // addrA.
Qed.

Arguments addXn_const _ _ _ _ _ _ _ _ _ _ _ n a q : simpl never. 

Lemma addXnE n p q : to_poly (addXn n p q) = to_poly p * 'X^n + to_poly q.
Proof.
elim: p n q => [a n q|a n' p ih n [b|b m q]] /=; simpC; first by rewrite addXn_constE.
  case: eqP => [->|/eqP n0]; first by rewrite expr0 mulr1 /= polyC_add addrA.
  by rewrite /= /cast /cast_pos_nat /cast_nat_pos insubdK // -topredE /= lt0n.
case: eqP => [->|/eqP no].
  rewrite expr0 mulr1 /lt_op /lt_pos /eq_op /eq_pos.
  case: ifP => [/eqP ->|hneq] /=.
    by rewrite ih expr0 mulr1 mulrDl polyC_add -!addrA [_ + (a%:P + _)]addrCA.
  have [hlt|hleq] /= := ltnP; rewrite ih polyC_add mulrDl -!addrA ?expr0.
    rewrite mulr1 /= addr0 -mulrA -exprD [_ + (a%:P + _)]addrCA /cast.
    by rewrite /cast_pos_nat insubdK ?subnK -?topredE /= ?subn_gt0 // ltnW. 
  rewrite -mulrA -exprD [_ + (a%:P + _)]addrCA /cast /cast_pos_nat.
  rewrite  insubdK ?subnK // -?topredE /= subn_gt0; rewrite leq_eqVlt in hleq.
  by case/orP: hleq hneq => // /eqP /val_inj ->; rewrite eqxx.
rewrite !ih !addXn_constE expr0 mulr1 /= addr0 mulrDl -mulrA -exprD addnC.
by rewrite -!addrA [b%:P + (_ + _)]addrCA [b%:P + _]addrC.
Qed.

Instance refines_addhpoly : param (Rhpoly ==> Rhpoly ==> Rhpoly) +%R +%C.
Proof. 
apply param_abstr2 => p hp h1 q hq h2.
rewrite [p]RhpolyE [q]RhpolyE paramE /Rhpoly /fun_hrel {p q h1 h2}.
by rewrite /add_op /add_hpoly addXnE expr0 mulr1.
Qed.

Instance refines_hpoly_scale : param (Logic.eq ==> Rhpoly ==> Rhpoly) *:%R *:%C.
Proof.
rewrite paramE => /= a b -> p hp h1.
rewrite [p]RhpolyE /Rhpoly /fun_hrel {a p h1}.
elim: hp => [a|a n p ih] /=; first by rewrite polyC_mul mul_polyC.
by rewrite ih polyC_mul -!mul_polyC mulrDr mulrA.
Qed.

Instance refines_hpolymul : param (Rhpoly ==> Rhpoly ==> Rhpoly) *%R *%C.
Proof. 
apply param_abstr2 => p hp h1 q hq h2.
rewrite [p]RhpolyE [q]RhpolyE paramE /Rhpoly /fun_hrel {p q h1 h2}.
elim: hp hq => [a [b|b m q]|a n p ih [b|b m q]] /=; rewrite ?polyC_mul //.
    by rewrite mulrDr mulrA !mul_polyC -[to_poly _]RhpolyE. 
  by rewrite mulrDl -[to_poly _]RhpolyE ![_ * b%:P]mulrC mulrA !mul_polyC.
rewrite mulrDr !mulrDl mulrCA -!mulrA -exprD mulrCA !mulrA [_ * _ * b%:P]mulrC.
rewrite -polyC_mul !mul_polyC /mul_op /= /add_op /add_hpoly !addXnE /= expr0.
rewrite !mulr1 !addr0 ih -?[to_poly (_ *: _)%C]RhpolyE.
rewrite scalerAl /add_pos /cast /cast_pos_nat insubdK //.
by rewrite -topredE /= addn_gt0; case: n => /= x ->.
Qed.

Instance refines_hpolysub : param (Rhpoly ==> Rhpoly ==> Rhpoly) subr sub_op.
Proof.
apply param_abstr2 => p hp h1 q hq h2.
by rewrite paramE /sub_op /sub_hpoly /Rhpoly /fun_hrel -[to_poly _]RhpolyE.
Qed.

(* Instance refines_hpoly_eq : param (Rhpoly ==> Rhpoly ==> Logic.eq)  *)
(*   (fun p q => p == q) (fun hp hq => hp == hq)%C. *)
(* Proof. *)
(* apply param_abstr2 => p hp h1 q hq h2. *)
(* by rewrite /eq_op /eq_hpoly paramE -[eq0_hpoly _]RboolE subr_eq0. *)
(* Qed. *)

(* Maybe Logic.eq is not right here? Maybe we should have refines for pos? *)
Instance refines_shift_hpoly : param (Logic.eq ==> Rhpoly ==> Rhpoly) 
  (fun n p => p * 'X^(cast n)) (fun n p => shift_hpoly n p).
Proof.
rewrite paramE => /= a n -> p hp h1.
by rewrite [p]RhpolyE /Rhpoly /fun_hrel {a p h1} /= addr0.
Qed.

(* Instance refines_size_hpoly : param (Rhpoly ==> Logic.eq)  *)
(*   (fun p => size p) (fun p => size_hpoly p). *)
(* Proof. *)
(* apply param_abstr => /= p hp h1. *)
(* rewrite [p]RhpolyE paramE /Rhpoly /fun_hrel {p h1}. *)
(* elim: hp => [a|a n p ih] /=. *)
(*   by rewrite size_polyC; simpC; case: eqP. *)
(* rewrite size_MXnaddC ih. *)
(* admit. *)
(* Qed. *)


(*************************************************************************)
(* PART III: Parametricity part                                          *)
(*************************************************************************)
Section hpoly_parametricity.

Import Refinements.Op.

Context (C : Type) (rAC : A -> C -> Prop).
Context `{zero C, one C, opp C, add C, sub C, mul C, eq C}.
Context `{!param rAC 0%R 0%C, !param rAC 1%R 1%C}.
Context `{!param (rAC ==> rAC) -%R -%C}.
Context `{!param (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!param (rAC ==> rAC ==> rAC) subr sub_op}.
Context `{!param (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!param (rAC ==> rAC ==> Logic.eq) eqtype.eq_op eq_op}.

(* TODO: Write this section! *)

(* Definition RhpolyC := (Rhpoly \o (seq_hrel rAC))%rel. *)

(* Global Instance param_zero_hpoly : param RhpolyC 0%R 0%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance param_one_hpoly : param RhpolyC 1%R 1%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance param_opp_hpoly :  *)
(*   param (RhpolyC ==> RhpolyC) -%R -%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance param_add_hpoly :  *)
(*   param (RhpolyC ==> RhpolyC ==> RhpolyC) +%R +%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance param_sub_hpoly :  *)
(*   param (RhpolyC ==> RhpolyC ==> RhpolyC) subr sub_op. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance param_scale_hpoly : *)
(*   param (rAC ==> RhpolyC ==> RhpolyC) *:%R *:%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance param_shift_hpoly : param (Logic.eq ==> RhpolyC ==> RhpolyC)  *)
(*   (fun n p => p * 'X^n) (fun n => shift n). *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance param_size_hpoly : param (RhpolyC ==> Logic.eq)  *)
(*   (fun (p : {poly R}) => size p) (fun s => size_hpoly s). *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance param_lead_coef_hpoly :  *)
(*   param (RhpolyC ==> rAC) lead_coef (fun p => lead_coef_hpoly p). *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance param_polyC_hpoly :  *)
(*   param (rAC ==> RhpolyC) (fun a => a%:P) (fun a => cast a)%C. *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance param_mul_hpoly :  *)
(*   param (RhpolyC ==> RhpolyC ==> RhpolyC) *%R *%C. *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance param_eq_hpoly : param (RhpolyC ==> RhpolyC ==> Logic.eq)  *)
(*   (fun p q => p == q) (fun sp sq => sp == sq)%C. *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance param_horner_hpoly : param (RhpolyC ==> rAC ==> rAC)  *)
(*   (fun p x => p.[x]) (fun sp x => horner_seq sp x). *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

End hpoly_parametricity.
End hpoly_theory.