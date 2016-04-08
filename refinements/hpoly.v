(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

From CoqEAL Require Import param refinements pos hrel poly_op.

(******************************************************************************)
(** This file implements sparse polynomials in sparse Horner normal form.     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

(******************************************************************************)
(** PART I: Defining generic datastructures and programming with them         *)
(******************************************************************************)
Section hpoly.

Context {A N pos : Type}.

Inductive hpoly A := Pc : A -> hpoly A
                   | PX : A -> pos -> hpoly A -> hpoly A.

Section hpoly_op.

Context `{zero_of A, one_of A, add_of A, sub_of A, opp_of A, mul_of A, eq_of A}.
Context `{one_of pos, add_of pos, sub_of pos, eq_of pos, leq_of pos(*, lt_of pos*)}.
Context `{zero_of N, one_of N, eq_of N, leq_of N(*, lt_of N*), add_of N, sub_of N}.
Context `{cast_of N pos, cast_of pos N}.

Local Open Scope computable_scope.

Fixpoint normalize (p : hpoly A) : hpoly A := match p with
  | Pc c => Pc c
  | PX a n p => match normalize p with
    | Pc c => PX a n (Pc c)
    | PX b m q => if (b == 0)%C then PX a (m + n) q else PX a n (PX b m q)
    end
  end.

Fixpoint from_seq (p : seq A) : hpoly A := match p with
  | [::] => Pc 0
  | [:: c] => Pc c
  | x :: xs => PX x 1 (from_seq xs)
  end.

Global Instance cast_hpoly : cast_of A (hpoly A) := fun x => Pc x.

Global Instance zero_hpoly : zero_of (hpoly A) := Pc 0.
Global Instance one_hpoly  : one_of (hpoly A)  := Pc 1.

Fixpoint map_hpoly A B (f : A -> B) (p : hpoly A) : hpoly B := match p with
  | Pc c     => Pc (f c)
  | PX a n p => PX (f a) n (map_hpoly f p)
  end.

Global Instance opp_hpoly : opp_of (hpoly A) := map_hpoly -%C.
Global Instance scale_hpoly : scale_of A (hpoly A) :=
  fun a => map_hpoly [eta *%C a].

Fixpoint addXn_const (n : N) a (q : hpoly A) := match q with
  | Pc b      => if (n == 0)%C then Pc (a + b) else PX b (cast n) (Pc a)
  | PX b m q' => let cn := cast n in
    if (n == 0)%C then PX (a + b) m q' else
      if (n == cast m)%C    then PX b m (addXn_const 0 a q') else
        if (*n < cast m*) (n <= cast m)%C && ~~(n == cast m)%C
        then PX b cn (PX a (m - cn) q')
                    else PX b m (addXn_const (n - cast m)%C a q')
  end.

Fixpoint addXn (n : N) p q {struct p} := match p, q with
  | Pc a      , q      => addXn_const n a q
  | PX a n' p', Pc b   => if (n == 0)%C then PX (a + b) n' p'
                                        else PX b (cast n) (PX a n' p')
  | PX a n' p', PX b m q' =>
    if (n == 0)%C then
      if (n' == m)%C then PX (a + b) n' (addXn 0 p' q') else
        if (*n' < m*) (n' <= m)%C && ~~(n' == m)%C
        then PX (a + b) n' (addXn 0 p' (PX 0 (m - n') q'))
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

Global Instance add_hpoly : add_of (hpoly A) := addXn 0.
Global Instance sub_hpoly : sub_of (hpoly A) := fun p q => p + - q.

Global Instance shift_hpoly : shift_of (hpoly A) N :=
  fun n p => if (n == 0)%C then p else PX 0 (cast n) p.

Global Instance mul_hpoly : mul_of (hpoly A) := fix f p q := match p, q with
  | Pc a, q => a *: q
  | p, Pc b => b *: p
  | PX a n p, PX b m q =>
     shift_hpoly (cast (n + m)) (f p q) + shift_hpoly (cast m) (a *: q) +
    (shift_hpoly (cast n) (b *: p) + Pc (a * b))
  end.

Fixpoint eq0_hpoly (p : hpoly A) : bool := match p with
  | Pc a      => (a == 0)%C
  | PX a n p' => (eq0_hpoly p') && (a == 0)%C
  end.

Global Instance eq_hpoly : eq_of (hpoly A) := fun p q => eq0_hpoly (p - q).

(* Alternative definition, should be used with normalize: *)
(* Fixpoint eq_hpoly_op p q {struct p} := match p, q with *)
(*   | Pc a, Pc b => (a == b)%C *)
(*   | PX a n p', PX b m q' => (a == b)%C && (cast n == cast m) && (eq_hpoly_op p' q') *)
(*   | _, _ => false *)
(*   end. *)

Global Instance size_hpoly : size_of (hpoly A) N :=
  fix f p :=
    if eq0_hpoly p then 0%C else match p with
                                 | Pc a => 1%C
                                 | PX a n p' => if eq0_hpoly p' then 1%C
                                                else (cast n + f p')%C
                                 end.

Global Instance lead_coef_hpoly : lead_coef_of A (hpoly A) :=
  fix f p :=
    match p with
    | Pc a => a
    | PX a n p' => let b := f p' in
                   if (b == 0)%C then a else b
    end.

Global Instance split_hpoly : split_of (hpoly A) N :=
  fix f m p:=
    if (m == 0)%C then (p, Pc 0)%C else
      match p with
      | Pc a => (Pc 0, Pc a)
      | PX a n p' => if (cast n <= m)%C
                     then let (p1, p2) := f (m - cast n)%C p' in
                          (p1, PX a n p2)
                     else (shift_hpoly (cast n - m)%C p', Pc a)
      end.

End hpoly_op.
End hpoly.

Parametricity hpoly.
Parametricity normalize.
Parametricity from_seq.
Parametricity cast_hpoly.
Parametricity zero_hpoly.
Parametricity one_hpoly.
Parametricity map_hpoly.
Parametricity opp_hpoly.
Parametricity scale_hpoly.
Parametricity addXn_const.
Parametricity addXn.
Parametricity add_hpoly.
Parametricity sub_hpoly.
Parametricity shift_hpoly.
Parametricity mul_hpoly.
Parametricity eq0_hpoly.
Parametricity eq_hpoly.
Parametricity size_hpoly.
Parametricity lead_coef_hpoly.
Parametricity split_hpoly.

Section hpoly_more_op.

Variable R : ringType.
Context (pos N C: Type).
Context `{zero_of C, one_of C, eq_of C}.
Context `{spec_of C R, spec_of N nat}.
Context `{cast_of pos N}.

Fixpoint spec_hpoly_aux n (p : @hpoly pos C) : {poly R} :=
  match p with
  | Pc c => match n with
            | O => if (c == 0)%C then 0 else if (c == 1)%C then 1
                                             else (spec c)%:P
            | S O => if (c == 0)%C then 0 else if (c == 1)%C then 'X
                                               else (spec c) *: 'X
            | S m => if (c == 0)%C then 0 else if (c == 1)%C then 'X^(S m)
                                               else (spec c) *: 'X^(S m)
            end
  | PX a m p => let mon := match n with
                           | O => if (a == 0)%C then 0
                                  else if (a == 1)%C then 1 else (spec a)%:P
                           | S O => if (a == 0)%C then 0
                                    else if (a == 1)%C then 'X
                                         else (spec a) *: 'X
                           | S k => if (a == 0)%C then 0
                                    else if (a == 1)%C then 'X^(S k)
                                         else (spec a) *: 'X^(S k)
                           end
                in if (eq0_hpoly p) then mon
                   else
                     let k := if (n == 0)%N then (spec (cast m : N) : nat)
                              else (spec (cast m : N) + n)%N
                     in if (a == 0)%C then (spec_hpoly_aux k p) else
                          (spec_hpoly_aux k p) + mon
  end.

Global Instance spec_hpoly : spec_of (hpoly C) {poly R} := spec_hpoly_aux 0%N.

Lemma spec_aux_shift n p :
  spec_hpoly_aux n p = spec_hpoly_aux 0%N p * 'X^n.
Proof.
  have shift_polyC (c : C) m :
    match m with
    | O => if (c == 0)%C then 0 else if (c == 1)%C then 1
                                     else (spec c)%:P
    | S O => if (c == 0)%C then 0 else if (c == 1)%C then 'X : {poly R}
                                       else (spec c) *: 'X
    | S m => if (c == 0)%C then 0 else if (c == 1)%C then 'X^(S m)
                                       else (spec c) *: 'X^(S m)
    end = (if (c == 0)%C then 0 else if (c == 1)%C then 1 else (spec c)%:P) *
          'X^m.
    case: m=> [|m] /=; first by rewrite expr0 mulr1.
    by case: m=> [|m] /=; rewrite ?expr1 -mul_polyC;
      case: ifP=> _; rewrite ?mul0r //;
        case: ifP=> _; rewrite ?mul1r.
  elim: p n=> [c n|c m p ih n] //=.
  case: ifP=> _ //.
  have -> : (if (n == 0)%N then (spec (cast m : N) : nat)
             else (spec (cast m : N) + n)%N) = (spec (cast m : N) + n)%N.
    by case: n=> [|n] /=; rewrite ?addn0.
  rewrite shift_polyC ih [in RHS]ih.
  by case: ifP=> c0;
    rewrite ?mulrDl -mulrA -exprD // c0.
Qed.

Lemma spec_aux_eq0 p : eq0_hpoly p -> spec_hpoly_aux 0%N p = 0.
Proof.
  elim: p=> [c|c m p ih] /=; first by move->.
  move/andP=> heq0.
  by rewrite (proj1 heq0) (proj2 heq0).
Qed.

End hpoly_more_op.

Arguments spec_hpoly / : assert.

(******************************************************************************)
(** PART II: Proving correctness properties of the previously defined objects *)
(******************************************************************************)
Section hpoly_theory.

Variable A : comRingType.

Instance zeroA : zero_of A   := 0%R.
Instance oneA  : one_of A    := 1%R.
Instance addA  : add_of A    := +%R.
Instance oppA  : opp_of A    := -%R.
Instance subA  : sub_of A    := fun x y => x - y.
Instance mulA  : mul_of A    := *%R.
Instance eqA   : eq_of A     := eqtype.eq_op.
Instance specA : spec_of A A := spec_id.

Instance zero_nat : zero_of nat     := 0%N.
Instance eq_nat   : eq_of nat       := eqtype.eq_op.
(* Instance lt_nat   : lt nat       := ltn. *)
Instance leq_nat  : leq_of nat      := ssrnat.leq.
Instance add_nat  : add_of nat      := addn.
Instance sub_nat  : sub_of nat      := subn.
Instance spec_nat : spec_of nat nat := spec_id.

Fixpoint to_poly (p : hpoly A) := match p with
  | Pc c => c%:P
  | PX a n p => to_poly p * 'X^(cast (n : pos)) + a%:P
  end.

Definition to_hpoly : {poly A} -> (@hpoly pos A) := fun p => from_seq (polyseq p).

(* This instance has to be declared here in order not to make form_seq confused *)
Instance one_nat  : one_of nat  := 1%N.

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

Lemma ncons_add : forall m n (a : A) p,
  ncons (m + n) a p = ncons m a (ncons n a p).
Proof. by elim=> //= m ih n a p; rewrite ih. Qed.

Lemma normalizeK : forall p, to_poly (normalize p) = to_poly p.
Proof.
elim => //= a n p <-; case: (normalize p) => //= b m q.
case: ifP => //= /eqP ->; case: n => [[]] //= n n0.
by rewrite addr0 /cast /cast_pos_nat insubdK /= ?exprD ?mulrA ?addnS.
Qed.

Definition Rhpoly : {poly A} -> hpoly A -> Type := fun_hrel to_poly.

(* This is OK here, but not everywhere *)
Instance refines_eq_refl A (x : A) : refines Logic.eq x x | 999.
Proof. by rewrite refinesE. Qed.

Lemma RhpolyE p q : refines Rhpoly p q -> p = to_poly q.
Proof. by rewrite refinesE. Qed.

Instance Rhpolyspec_r x : refines Rhpoly (to_poly x) x | 10000.
Proof. by rewrite !refinesE; case: x. Qed.

Fact normalize_lock : unit. Proof. exact tt. Qed.
Definition normalize_id := locked_with normalize_lock (@id {poly A}).
Lemma normalize_idE p : normalize_id p = p.
Proof. by rewrite /normalize_id unlock. Qed.

Local Open Scope rel_scope.

Instance Rhpoly_normalize : refines (Rhpoly ==> Rhpoly) normalize_id normalize.
Proof.
  by rewrite refinesE => p hp rp;
    rewrite /Rhpoly /fun_hrel normalizeK normalize_idE.
Qed.

Instance Rhpoly_cast : refines (eq ==> Rhpoly) (fun x => x%:P) cast.
Proof.
  by rewrite refinesE=> _ x ->; rewrite /Rhpoly /fun_hrel /cast /cast_hpoly /=.
Qed.

(* zero and one *)
Instance Rhpoly_0 : refines Rhpoly 0%R 0%C.
Proof. by rewrite refinesE. Qed.

Instance Rhpoly_1 : refines Rhpoly 1%R 1%C.
Proof. by rewrite refinesE. Qed.

Instance Rhpoly_opp : refines (Rhpoly ==> Rhpoly) -%R -%C.
Proof.
apply refines_abstr => p hp h1.
rewrite [p]RhpolyE refinesE /Rhpoly /fun_hrel {p h1}.
by elim: hp => /= [a|a n p ->]; rewrite polyC_opp // opprD mulNr.
Qed.

Instance Rhpoly_scale : refines (Logic.eq ==> Rhpoly ==> Rhpoly) *:%R *:%C.
Proof.
rewrite refinesE => /= a b -> p hp h1.
rewrite [p]RhpolyE /Rhpoly /fun_hrel {a p h1}.
elim: hp => [a|a n p ih] /=; first by rewrite polyC_mul mul_polyC.
by rewrite ih polyC_mul -!mul_polyC mulrDr mulrA.
Qed.

Lemma addXn_constE n a q :
  to_poly (addXn_const n a q) = a%:P * 'X^n + to_poly q.
Proof.
elim: q n => [b [|n]|b m q' ih n] /=; simpC;
  first by rewrite polyC_add expr0 mulr1.
  by rewrite /cast /cast_pos_nat insubdK.
case: eqP => [->|/eqP n0] /=; first by rewrite polyC_add expr0 mulr1 addrCA.
case: eqP => [hn|hnc] /=; first by rewrite ih expr0 mulr1 -hn mulrDl -addrA.
rewrite [(_ <= _)%C]/((_ <= _)%N) subn_eq0.
have [hleq|hlt] /= := leqP n (cast m);
  rewrite /cast /cast_nat_pos /cast_pos_nat.
  rewrite insubdK -?topredE /= ?lt0n // mulrDl -mulrA -exprD addrCA -addrA.
  rewrite ?insubdK -?topredE /= ?subn_gt0 ?lt0n ?subnK // ltn_neqAle.
  by move/eqP: hnc=> ->.
by rewrite ih mulrDl -mulrA -exprD subnK ?addrA // ltnW.
Qed.

Arguments addXn_const _ _ _ _ _ _ _ _ _ _ _ n a q : simpl never.

Lemma addXnE n p q : to_poly (addXn n p q) = to_poly p * 'X^n + to_poly q.
Proof.
elim: p n q => [a n q|a n' p ih n [b|b m q]] /=; simpC;
  first by rewrite addXn_constE.
  case: eqP => [->|/eqP n0]; first by rewrite expr0 mulr1 /= polyC_add addrA.
  by rewrite /= /cast /cast_pos_nat /cast_nat_pos insubdK // -topredE /= lt0n.
case: eqP => [->|/eqP no].
  rewrite expr0 mulr1 /leq_op /leq_pos /eq_op /eq_pos.
  case: ifP => [/eqP ->|hneq] /=.
    by rewrite ih expr0 mulr1 mulrDl polyC_add -!addrA [_ + (a%:P + _)]addrCA.
  rewrite hneq.
  have [hlt|hleq] /= := leqP (val_of_pos n') (val_of_pos m);
    rewrite ih polyC_add mulrDl -!addrA ?expr0.
    rewrite mulr1 /= addr0 -mulrA -exprD [_ + (a%:P + _)]addrCA /cast.
    rewrite /cast_pos_nat insubdK ?subnK -?topredE /= ?subn_gt0 // ltn_neqAle.
    by move/eqP/eqP: hneq=> ->.
  rewrite -mulrA -exprD [_ + (a%:P + _)]addrCA /cast /cast_pos_nat.
  rewrite  insubdK ?subnK // -?topredE /=; first by rewrite ltnW.
  by rewrite subn_gt0.
rewrite !ih !addXn_constE expr0 mulr1 /= addr0 mulrDl -mulrA -exprD addnC.
by rewrite -!addrA [b%:P + (_ + _)]addrCA [b%:P + _]addrC.
Qed.

Instance Rhpoly_add :
  refines (Rhpoly ==> Rhpoly ==> Rhpoly) +%R (add_hpoly (N:=nat)).
Proof.
apply refines_abstr2 => p hp h1 q hq h2.
rewrite [p]RhpolyE [q]RhpolyE refinesE /Rhpoly /fun_hrel {p q h1 h2}.
by rewrite /add_op /add_hpoly addXnE expr0 mulr1.
Qed.

Lemma to_poly_scale a p : to_poly (a *: p)%C = a *: (to_poly p).
Proof.
  elim: p=> [b|b n p ih] /=;
    rewrite /mul_op /mulA -mul_polyC polyC_mul //.
  by rewrite ih -mul_polyC mulrDr mulrA /mul_op /mulA.
Qed.

Lemma cast_nat_posK n : n > 0 -> cast_pos_nat (cast_nat_pos n) = n.
Proof.
  by rewrite /cast_pos_nat /cast_nat_pos val_insubd=> ->.
Qed.

Instance Rhpoly_mul :
  refines (Rhpoly ==> Rhpoly ==> Rhpoly) *%R (mul_hpoly (N:=nat)).
Proof.
apply refines_abstr2 => p hp h1 q hq h2.
rewrite [p]RhpolyE [q]RhpolyE refinesE /Rhpoly /fun_hrel {p q h1 h2}.
elim: hp hq => [a [b|b m l']|a n l ih [b|b m l']] /=;
      first by rewrite polyC_mul.
    by rewrite polyC_mul to_poly_scale -mul_polyC mulrDr mulrA.
  by rewrite polyC_mul to_poly_scale -mul_polyC mulrDl -mulrA mulrC
             [(_%:P * _%:P)]mulrC.
rewrite [in (cast _)]/add_op /add_pos.
case: n=> n lt0n; case: m=> m lt0m /=.
rewrite /cast cast_nat_posK /cast_pos_nat ?addn_gt0 ?lt0n //= /shift_hpoly.
simpC; rewrite !gtn_eqF ?addn_gt0 ?lt0n //=.
rewrite mulrDr !mulrDl mulrCA -!mulrA -exprD mulrCA !mulrA [_ * b%:P]mulrC.
rewrite -polyC_mul !mul_polyC !addXnE /= expr0 !mulr1 !addr0 ih scalerAl /cast.
by rewrite !to_poly_scale !cast_nat_posK ?addn_gt0 ?lt0n.
Qed.

Instance Rhpoly_sub :
  refines (Rhpoly ==> Rhpoly ==> Rhpoly) (fun x y => x - y)
          (sub_hpoly (N:=nat)).
Proof.
apply refines_abstr2 => p hp h1 q hq h2.
by rewrite refinesE /sub_hpoly /Rhpoly /fun_hrel [_ - _]RhpolyE.
Qed.

Instance Rhpoly_shift : refines (Logic.eq ==> Rhpoly ==> Rhpoly)
                                (shiftp (R:=A)) shift_op.
Proof.
  rewrite refinesE=> _ n -> p hp h1.
  rewrite [p]RhpolyE /Rhpoly /fun_hrel {p h1} /shiftp /shift_hpoly.
  case: n=> [|n] /=; first by rewrite expr0 mulr1.
  by rewrite addr0 /cast cast_nat_posK ?ltn0Sn.
Qed.

(* Add to ssr? *)
Lemma size_MXnaddC (R : comRingType) (p : {poly R}) (c : R) n :
  size (p * 'X^n.+1 + c%:P) = if (p == 0) then size c%:P else (n.+1 + size p)%N.
Proof.
have [->|/eqP hp0] := eqP; first by rewrite mul0r add0r.
rewrite size_addl polyseqMXn ?size_ncons // size_polyC.
by case: (c == 0)=> //=; rewrite ltnS ltn_addl // size_poly_gt0.
Qed.

Instance Rhpoly_eq0 :
  refines (Rhpoly ==> bool_R) (fun p => 0 == p) eq0_hpoly.
Proof.
  rewrite refinesE => p hp rp; rewrite [p]RhpolyE {p rp} eq_sym.
  have -> : (to_poly hp == 0) = (eq0_hpoly hp).
    elim: hp => [a|a n p ih] /=; first by rewrite polyC_eq0.
    rewrite /cast /cast_pos_nat /=; case: n=> n ngt0.
    rewrite /val_of_pos -[n]prednK // -size_poly_eq0 size_MXnaddC -ih prednK //.
    case: ifP=> /=; first by rewrite size_poly_eq0 polyC_eq0.
    by rewrite addn_eq0 size_poly_eq0 andbC=> ->.
  exact: bool_Rxx.
Qed.

Instance Rhpoly_eq : refines (Rhpoly ==> Rhpoly ==> bool_R)
                             eqtype.eq_op (eq_hpoly (N:=nat)).
Proof.
  apply refines_abstr2=> p hp h1 q hq h2.
  rewrite /eq_hpoly refinesE -subr_eq0 eq_sym [_ == _]refines_eq.
  exact: bool_Rxx.
Qed.

Instance Rhpoly_size : refines (Rhpoly ==> Logic.eq) (sizep (R:=A)) size_op.
Proof.
  apply refines_abstr=> p hp h1.
  rewrite [p]RhpolyE refinesE {p h1} sizepE /size_op.
  elim: hp=> [a|a n p ih] /=; first by rewrite size_polyC; simpC; case: eqP.
  rewrite /cast /cast_pos_nat /=; case: n=> n ngt0.
  rewrite /val_of_pos -[n]prednK // size_MXnaddC ih prednK // eq_sym
          [_ == _]refines_eq.
  by case: ifP=> //=; simpC; rewrite size_polyC; case: ifP.
Qed.

Lemma lead_coef_MXnaddC (R : comRingType) (p : {poly R}) (c : R) n :
  lead_coef (p * 'X^n.+1 + c%:P) = if (lead_coef p == 0) then c
                                   else lead_coef p.
Proof.
  have [|/eqP hp0] := eqP.
    move/eqP; rewrite lead_coef_eq0; move/eqP=> ->.
    by rewrite mul0r add0r lead_coefC.
  rewrite lead_coefDl; first by rewrite lead_coef_Mmonic ?monicXn.
  rewrite size_polyC size_Mmonic ?monicXn -?lead_coef_eq0 //.
  rewrite size_polyXn !addnS -pred_Sn.
  case: (c == 0)=> //=.
  by rewrite ltnS ltn_addr // size_poly_gt0 -lead_coef_eq0.
Qed.

Instance Rhpoly_lead_coef : refines (Rhpoly ==> Logic.eq)
                                    lead_coef lead_coef_op.
Proof.
  rewrite /lead_coef_op refinesE=> _ hp <-.
  elim: hp=> [a|a n p ih] /=; first by rewrite lead_coefC.
  rewrite -ih /cast /cast_pos_nat /=; case: n=> n ngt0.
  by rewrite /val_of_pos -[n]prednK // lead_coef_MXnaddC.
Qed.

Lemma rdivpXnSm (p : {poly A}) a n m :
  rdivp (p * 'X^n + a%:P) 'X^m.+1 = if (n <= m.+1)%C then rdivp p 'X^(m.+1 - n)
                                    else p * 'X^(n - m.+1).
Proof.
  have [leqnSm|gtnSm] := leqP n m.+1.
    rewrite [(_ <= _)%C]leqnSm.
    rewrite [p in LHS](@rdivp_eq _ 'X^(m.+1 - n)) ?monicXn //.
    rewrite mulrDl -addrA -mulrA -exprD subnK ?rdivp_addl_mul_small //.
      by rewrite monicXn.
    rewrite size_polyXn (leq_ltn_trans (size_add _ _)) // gtn_max.
    rewrite (leq_ltn_trans (size_mul_leq _ _)) /=.
      by rewrite size_polyC; case: (a != 0).
    rewrite size_polyXn addnS -pred_Sn addnC -ltn_subRL [X in (_ < X)]subSn //.
    by rewrite -[X in (_ < X)](size_polyXn A) ltn_rmodp monic_neq0 ?monicXn.
  rewrite ifN -?ltnNge // -[in LHS](subnK (ltnW gtnSm)) exprD mulrA.
  by rewrite rdivp_addl_mul_small ?monicXn ?size_polyC ?size_polyXn;
    case: (a != 0).
Qed.

Lemma rmodpXnSm (p : {poly A}) a n m :
  rmodp (p * 'X^n + a%:P) 'X^m.+1 =
  if (n <= m.+1)%C then (rmodp p 'X^(m.+1 - n)) * 'X^n + a%:P
  else a%:P.
Proof.
  have [leqnSm|gtnSm] := leqP n m.+1.
    rewrite [(_ <= _)%C]leqnSm.
    rewrite [p in LHS](@rdivp_eq _ 'X^(m.+1 - n)) ?monicXn //.
    rewrite mulrDl -addrA -mulrA -exprD subnK ?rmodp_addl_mul_small //.
      by rewrite monicXn.
    rewrite size_polyXn (leq_ltn_trans (size_add _ _)) // gtn_max.
    rewrite (leq_ltn_trans (size_mul_leq _ _)) /=.
      by rewrite size_polyC; case: (a != 0).
    rewrite size_polyXn addnS -pred_Sn addnC -ltn_subRL [X in (_ < X)]subSn //.
    by rewrite -[X in (_ < X)](size_polyXn A) ltn_rmodp monic_neq0 ?monicXn.
  rewrite ifN -?ltnNge // -[in LHS](subnK (ltnW gtnSm)) exprD mulrA.
  by rewrite rmodp_addl_mul_small ?monicXn ?size_polyC ?size_polyXn;
    case: (a != 0).
Qed.

Instance Rhpoly_split :
  refines (Logic.eq ==> Rhpoly ==> prod_hrel Rhpoly Rhpoly)
          (splitp (R:=A)) split_op.
Proof.
  rewrite refinesE=> _ m -> p hp h1.
  rewrite [p]RhpolyE /prod_hrel /Rhpoly /fun_hrel /splitp /split_op {p h1} /=.
  elim: hp m=> [a [|m]|a n p ih [|m]] /=; first by rewrite expr0 rdivp1 rmodp1.
      rewrite rdivp_small ?rmodp_small ?polyC0 // size_polyC size_polyXn;
      by case: (a != 0).
    by rewrite expr0 rdivp1 rmodp1.
  rewrite rdivpXnSm rmodpXnSm.
  case: ifP=> hnSm /=.
    have -> /= := surjective_pairing (split_hpoly (m.+1 - cast n)%C p).
    by have [-> ->] := ih (m.+1 - cast n)%C.
  rewrite /shift_hpoly [(_ == _)%C]subn_eq0 ifN /=.
  rewrite polyC0 addr0 /cast cast_nat_posK //.
    by rewrite subn_gt0 ltnNge [(_ <= _)%N]hnSm.
  by rewrite [(_ <= _)%N]hnSm.
Qed.

Instance Rhpoly_spec_l :
  refines (Rhpoly ==> Logic.eq) spec_id (spec_hpoly (N:=nat) (C:=A)).
Proof.
  rewrite refinesE /spec_id=> _ hp <-.
  have simp_polyC a :
    a%:P = (if a == 0 then 0 else if a == 1 then 1 else (specA a)%:P).
    case: ifP=> [/eqP a0|_]; first by rewrite a0 polyC0.
    case: ifP=> [/eqP a1|_]; first by rewrite a1 polyC1.
    by rewrite /specA /spec_id.
  elim: hp=> [a|a n p ih] /=; simpC.
    exact: simp_polyC.
  rewrite spec_aux_shift /spec_nat /spec_id ih /spec_hpoly.
  case: ifP=> p0.
    rewrite spec_aux_eq0 // mul0r add0r.
    exact: simp_polyC.
  case: ifP=> [/eqP a0|_]; first by rewrite a0 polyC0 addr0.
  by rewrite [in LHS]simp_polyC.
Qed.

(*************************************************************************)
(* PART III: Parametricity part                                          *)
(*************************************************************************)
Section hpoly_parametricity.

Import Refinements.Op.

Context (C : Type) (rAC : A -> C -> Type).
Context (P : Type) (rP : pos -> P -> Type).
Context (N : Type) (rN : nat -> N -> Type).
Context `{zero_of C, one_of C, opp_of C, add_of C, sub_of C, mul_of C, eq_of C}.
Context `{one_of P, add_of P, sub_of P, eq_of P(* , lt P *), leq_of P}.
Context `{zero_of N, one_of N, eq_of N(* , lt N *), leq_of N, add_of N, sub_of N}.
Context `{cast_of N P, cast_of P N}.
Context `{spec_of C A, spec_of N nat}.
Context `{!refines rAC 0%R 0%C, !refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) (fun x y => x - y) sub_op}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (rAC ==> Logic.eq) spec_id spec}.
Context `{!refines rP pos1 1%C}.
Context `{!refines (rP ==> rP ==> rP) add_pos +%C}.
Context `{!refines (rP ==> rP ==> rP) sub_pos sub_op}.
Context `{!refines (rP ==> rP ==> bool_R) eqtype.eq_op eq_op}.
(* Context `{!refines (rP ==> rP ==> Logic.eq) lt_pos lt_op}. *)
Context `{!refines (rP ==> rP ==> bool_R) leq_pos leq_op}.
Context `{!refines rN 0%N 0%C, !refines rN 1%N 1%C}.
Context `{!refines (rN ==> rN ==> rN) addn +%C}.
Context `{!refines (rN ==> rN ==> rN) subn sub_op}.
Context `{!refines (rN ==> rN ==> bool_R) eqtype.eq_op eq_op}.
(* Context `{!refines (rN ==> rN ==> Logic.eq) ltn lt_op}. *)
Context `{!refines (rN ==> rN ==> bool_R) ssrnat.leq leq_op}.
Context `{!refines (rN ==> rP) cast_nat_pos cast}.
Context `{!refines (rP ==> rN) cast_pos_nat cast}.
Context `{!refines (rN ==> Logic.eq) spec_id spec}.

Definition RhpolyC := (Rhpoly \o (hpoly_R rP rAC)).

Global Instance RhpolyC_0 : refines RhpolyC 0%R 0%C.
Proof. param_comp zero_hpoly_R. Qed.

Global Instance RhpolyC_1 : refines RhpolyC 1%R 1%C.
Proof. param_comp one_hpoly_R. Qed.

Global Instance RhpolyC_add : refines (RhpolyC ==> RhpolyC ==> RhpolyC)
                                      +%R (add_hpoly (N:=N)).
Proof. param_comp add_hpoly_R. Qed.

Global Instance RhpolyC_opp : refines (RhpolyC ==> RhpolyC) -%R -%C.
Proof. param_comp opp_hpoly_R. Qed.

Global Instance RhpolyC_sub : refines (RhpolyC ==> RhpolyC ==> RhpolyC)
                                      (fun x y => x - y) (sub_hpoly (N:=N)).
Proof. param_comp sub_hpoly_R. Qed.

Global Instance RhpolyC_mul :
  refines (RhpolyC ==> RhpolyC ==> RhpolyC) *%R (mul_hpoly (N:=N)).
Proof. param_comp mul_hpoly_R. Qed.

Global Instance RhpolyC_size :
  refines (RhpolyC ==> rN) (sizep (R:=A)) size_hpoly.
Proof. param_comp size_hpoly_R. Qed.

Global Instance RhpolyC_lead_coef :
  refines (RhpolyC ==> rAC) lead_coef lead_coef_op.
Proof.
  rewrite /lead_coef_op.
  param_comp lead_coef_hpoly_R.
Qed.

Global Instance RhpolyC_polyC :
  refines (rAC ==> RhpolyC) (fun a => a%:P) cast.
Proof. param_comp cast_hpoly_R. Qed.

Global Instance RhpolyC_eq : refines (RhpolyC ==> RhpolyC ==> bool_R)
                                     eqtype.eq_op (eq_hpoly (N:=N)).
Proof. param_comp eq_hpoly_R. Qed.

Global Instance RhpolyC_scale : refines (rAC ==> RhpolyC ==> RhpolyC) *:%R *:%C.
Proof. param_comp scale_hpoly_R. Qed.

Global Instance RhpolyC_shift : refines (rN ==> RhpolyC ==> RhpolyC)
                                        (shiftp (R:=A)) shift_hpoly.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE; do ?move=> ?*.
  eapply (shift_hpoly_R (N_R:=rN))=> // *;
  exact: refinesP.
Qed.

Global Instance RhpolyC_mulXn p sp n rn :
  refines rN n rn -> refines RhpolyC p sp ->
  refines RhpolyC (p * 'X^n) (shift_op rn sp).
Proof.
  move=> hn hp; rewrite -[_ * 'X^_]/(shiftp _ _).
  exact: refines_apply.
Qed.

Lemma mulXnC (p : {poly A}) n : p * 'X^n = 'X^n * p.
Proof.
  apply/polyP=> i.
  by rewrite coefMXn coefXnM.
Qed.

Global Instance RhpolyC_Xnmul p sp n rn :
  refines rN n rn -> refines RhpolyC p sp ->
  refines RhpolyC ('X^n * p) (shift_op rn sp).
Proof. rewrite -mulXnC; exact: RhpolyC_mulXn. Qed.

Global Instance RhpolyC_scaleXn c rc n rn :
  refines rN n rn -> refines rAC c rc ->
  refines RhpolyC (c *: 'X^n) (shift_op rn (cast rc)).
Proof.
  move=> hn hc; rewrite -mul_polyC -[_ * 'X^_]/(shiftp _ _).
  exact: refines_apply.
Qed.

Global Instance RhpolyC_mulX p sp :
  refines RhpolyC p sp -> refines RhpolyC (p * 'X) (shift_op (1%C : N) sp).
Proof. rewrite -['X]expr1; exact: RhpolyC_mulXn. Qed.

Global Instance RhpolyC_Xmul p sp :
  refines RhpolyC p sp -> refines RhpolyC ('X * p) (shift_op (1%C : N) sp).
Proof. rewrite -['X]expr1 -mulXnC; exact: RhpolyC_mulX. Qed.

Global Instance RhpolyC_scaleX c rc :
  refines rAC c rc ->
  refines RhpolyC (c *: 'X) (shift_op (1%C : N) (cast rc)).
Proof. rewrite -['X]expr1; exact: RhpolyC_scaleXn. Qed.

Global Instance RhpolyC_split :
  refines (rN ==> RhpolyC ==> prod_R RhpolyC RhpolyC)
          (splitp (R:=A)) split_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE; do ?move=> ?*.
  eapply (split_hpoly_R (N_R:=rN))=> // *;
    exact: refinesP.
Qed.

Global Instance RhpolyC_splitn n rn p sp :
  refines rN n rn -> refines RhpolyC p sp ->
  refines (prod_R RhpolyC RhpolyC) (splitp n p) (split_op rn sp).
Proof. by move=> hn hp; exact: refines_apply. Qed.

(* same as for seqpoly... maybe have a generic version + refinement instance in
   another file? *)
Definition eq_prod_hpoly (x y : (@hpoly P C * @hpoly P C)) :=
  (eq_hpoly (N:=N) x.1 y.1) && (eq_hpoly (N:=N) x.2 y.2).

Global Instance refines_prod_RhpolyC_eq :
  refines (prod_R RhpolyC RhpolyC ==> prod_R RhpolyC RhpolyC ==> bool_R)
          eqtype.eq_op eq_prod_hpoly.
Proof.
  rewrite refinesE=> x x' hx y y' hy.
  rewrite /eqtype.eq_op /eq_prod_hpoly /=.
  have -> : (x.1 == y.1) = (eq_hpoly (N:=N) x'.1 y'.1).
    exact: refines_eq.
  have -> : (x.2 == y.2) = (eq_hpoly (N:=N) x'.2 y'.2).
    exact: refines_eq.
  exact: bool_Rxx.
Qed.

Global Instance RhpolyC_X : refines RhpolyC 'X (shift_op (1%C : N) 1)%C.
Proof. rewrite -['X]mul1r; exact: RhpolyC_mulX. Qed.

Global Instance RhpolyC_Xn n rn :
  refines rN n rn -> refines RhpolyC 'X^n (shift_op rn 1)%C.
Proof. move=> hn; rewrite -['X^_]mul1r; exact: RhpolyC_mulXn. Qed.

(* Global Instance RhpolyC_horner : param (RhpolyC ==> rAC ==> rAC) *)
(*   (fun p x => p.[x]) (fun sp x => horner_seq sp x). *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

Global Instance RhpolyC_spec :
  refines (RhpolyC ==> eq) spec_id (spec_hpoly (N:=N) (C:=C)).
Proof.
  eapply refines_trans; tc.
  rewrite refinesE=> hp hq rpq.
  elim: rpq=> {hp hq} [a c rac|a c rac n m rnm hp hq rpq] /=;
    rewrite ![(a == _)%C]refines_eq /specA [spec_id _]refines_eq //=.
  have -> : eq0_hpoly hp = eq0_hpoly hq.
    elim: rpq=> [x y rxy|x y rxy k l rkl p q rpq ih];
      by rewrite /= [(_ == _)%C]refines_eq ?ih.
  rewrite /spec_nat [spec_id _]refines_eq.
  by rewrite ![spec_hpoly_aux (spec _) _]spec_aux_shift=> ->.
Qed.

End hpoly_parametricity.
End hpoly_theory.

Section testpoly.

From mathcomp Require Import ssrint.
From CoqEAL Require Import binnat binint.

Goal (0 == 0 :> {poly int}).
rewrite [_ == _]refines_eq.
by compute.
Abort.

(* (* This one does not work, but it works with type {poly {poly int}}... *) *)
(* Goal (0 == (0 : {poly {poly {poly int}}})). *)
(* rewrite [_ == _]refines_eq. *)
(* by compute. *)
(* Abort. *)

Goal (1 == 1 :> {poly int}).
rewrite [_ == _]refines_eq.
by compute.
Abort.

(* Goal (1 == (1 : {poly {poly {poly int}}})). *)
(* rewrite [_ == _]refines_eq. *)
(* by compute. *)
(* Abort. *)

Goal ((1 + 2%:Z *: 'X + 3%:Z *: 'X^2) + (1 + 2%:Z%:P * 'X + 3%:Z%:P * 'X^2)
      == (1 + 1 + (2%:Z + 2%:Z) *: 'X + (3%:Z + 3%:Z)%:P * 'X^2)).
rewrite -[X in (X == _)]/(spec_id _) [spec_id _]refines_eq /=.
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

Goal (1 + 2%:Z *: 'X + 3%:Z *: 'X^2 - (1 + 2%:Z *: 'X + 3%:Z *: 'X^2) == 0).
rewrite -[X in (X == _)]/(spec_id _) [spec_id _]refines_eq /=.
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X) == 1 + 4%:Z *: 'X + 4%:Z *: 'X^2).
rewrite [_ == _]refines_eq.
by compute.
Abort.

(* (1 + xy) * x = x + x^2y *)
Goal ((1 + 'X * 'X%:P) * 'X == 'X + 'X^2 * 'X%:P :> {poly {poly int}}).
rewrite -[X in (X == _)]/(spec_id _) [spec_id _]refines_eq /=.
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (sizep ('X^2 : {poly int}) ==
      sizep (- 3%:Z *: 'X^(sizep ('X : {poly int})))).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (sizep (1 + 2%:Z *: 'X + 3%:Z *: 'X^2) == 3).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X^(sizep (1 : {poly int}))) ==
      1 + 4%:Z *: 'X + 4%:Z *: 'X^(sizep (10%:Z *: 'X))).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (splitp 2 (1 + 2%:Z *: 'X + 3%:Z%:P * 'X^2 + 4%:Z *: 'X^3) ==
      (3%:Z%:P + 4%:Z *: 'X, 1 + 2%:Z%:P * 'X)).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (splitp (sizep ('X : {poly int}))
             (1 + 2%:Z *: 'X + 3%:Z%:P * 'X^2 + 4%:Z *: 'X^3) ==
      (3%:Z%:P + 4%:Z *: 'X, 1 + 2%:Z%:P * 'X)).
rewrite [_ == _]refines_eq.
by compute.
Abort.

End testpoly.