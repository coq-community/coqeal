(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Import Pdiv.Ring.

Local Open Scope ring_scope.

Require Import cssralg.

Section SeqPoly.

Variable R : comRingType.
Variable CR : cringType R.

Definition trans_poly (p : {poly R}) : seq CR :=
  [seq trans x | x <- polyseq p ].

Lemma inj_trans_poly : injective trans_poly.
Proof.
rewrite /trans_poly=> p q h.
apply/poly_inj.
move: (@inj_trans _ CR).
move/inj_map: h.
by apply.
Qed.

Definition poly_trans_struct := Trans inj_trans_poly.

Lemma trans_poly0 : trans_poly 0 = [::].
Proof. by rewrite /trans_poly polyseq0. Qed.

Lemma trans_poly1 : trans_poly 1 = [:: (one CR)].
Proof. by rewrite /trans_poly polyseq1 -oneE. Qed.

Lemma trans_poly_eq0 p : (trans_poly p == [::]) = (p == 0).
Proof.
apply/eqP/eqP=> [h|->].
  apply/inj_trans_poly.
  by rewrite h trans_poly0.
by rewrite trans_poly0.
Qed.

Lemma size_trans_poly : forall p, size (trans_poly p) = size p.
Proof.
rewrite /trans_poly.
case=> xs /= _.
by elim: xs => //= x xs ->.
Qed.

(* Reflection lemma *)
Lemma trans_polyP p q : reflect (p = q) (trans_poly p == trans_poly q).
Proof.
apply: (iffP idP)=> [|->] // /eqP.
exact: (@inj_trans_poly p q).
Qed.

(* Addition *)
Fixpoint add_seq p q := match p, q with
  | [::], _ => q
  | _, [::] => p
  | x :: xs, y :: ys =>
        let xy := add x y in
        let r  := add_seq xs ys
        in if xy == zero CR then if r == [::] then [::] else xy :: r else xy :: r
  end.

Lemma add_seqr0 : forall p, add_seq p [::] = p.
Proof. by case. Qed.

Lemma cons_poly_add (x y : R) xs ys :
  cons_poly x xs + cons_poly y ys = cons_poly (x + y) (xs + ys).
Proof.
by rewrite !cons_poly_def mulrDl addrCA polyC_add -!addrA addrCA.
Qed.

Lemma size_poly_neq0 (p : {poly R}) : (size p != 0%N) = (p != [::] :> seq R).
Proof. by rewrite (size_poly_eq0 p) -polyseq0. Qed.

Lemma add_seqE : {morph trans_poly : p q / p + q >-> add_seq p q}.
Proof.
rewrite /trans_poly.
elim/poly_ind=> [q| p c IH q].
  by rewrite add0r polyseq0.
elim/poly_ind: q => [| q d _] .
  by rewrite addr0 polyseq0 add_seqr0.
rewrite -!cons_poly_def cons_poly_add !polyseq_cons.
case: ifP => [|spq].
  case: ifP => sp.
    case: ifP => sq.
      rewrite size_poly_neq0 /= -addE trans_eq0.
      case: ifP; rewrite -IH //.
      move: (trans_poly_eq0 (p + q)).
      rewrite /trans_poly -polyseq0 => ->.
      by case: ifP=> // /eqP ->; rewrite eqxx.
    rewrite polyseqC.
    have q0: (q == 0) by move/negbT: sq; rewrite negbK nil_poly.
    case d0: (d == 0)=> /=; first by rewrite (eqP d0) (eqP q0) !addr0.
    rewrite -addE trans_eq0.
    rewrite (eqP q0) addr0 add_seqr0 size_poly_neq0 => /negbTE.
    move: (trans_poly_eq0 p).
    rewrite /trans_poly -polyseq0 => ->.
    do 2! case: ifP => //.
    by move/eqP->; rewrite eqxx.
  have p0: (p == 0) by move/negbT: sp; rewrite negbK nil_poly.
  rewrite (eqP p0) !add0r polyseqC=> H.
  rewrite H; rewrite size_poly_neq0 in H.
  case c0: (c == 0)=> /=; first by rewrite (eqP c0) add0r.
  move: H.
  rewrite -addE trans_eq0.
  move: (trans_poly_eq0 q).
  rewrite /trans_poly -polyseq0 => ->.
  do 2! case: ifP => //.
  by move/eqP->; rewrite eqxx.
move/negbT: spq.
rewrite negbK nil_poly addrC addr_eq0=> /eqP ->.
rewrite /nilp size_opp !polyseqC.
case: ifP=> h /=.
  by rewrite -IH subrr polyseq0 /= -addE trans_eq0; case: ifP.
case c0: (c == 0)=> /=; first by rewrite (eqP c0) add0r.
case d0: (d == 0)=> /=; first by rewrite (eqP d0) addr0 (negbT c0) /=.
by rewrite -addE trans_eq0; case: ifP.
Qed.

(* Negation *)
Definition opp_seq p : seq CR := [seq opp x | x <- p].

Lemma opp_cons_poly (c : R) p : -(cons_poly c p) = cons_poly (-c) (-p).
Proof.
rewrite !cons_poly_def.
apply/polyP=> i.
rewrite coef_opp_poly !coef_add_poly !coefMX.
case: i=> [|n].
  by rewrite eqxx !add0r polyC_opp coefN.
by rewrite coefN polyC_opp coefN opprD.
Qed.

Lemma opp_seqE : {morph trans_poly : p / - p >-> opp_seq p }.
Proof.
rewrite /trans_poly.
elim/poly_ind=> [|p c IH].
  by rewrite oppr0 polyseq0.
rewrite -!cons_poly_def opp_cons_poly !polyseq_cons /nilp size_opp.
case: ifP=> sp /=; first by rewrite -IH oppE.
by rewrite !polyseqC oppr_eq0; case: (c == 0) => //=; rewrite oppE.
Qed.

(* CZmodule structure *)
Definition seq_czMixin := @CZmodMixin
  [zmodType of {poly R}] (seq CR) [::]
  opp_seq add_seq poly_trans_struct trans_poly0 opp_seqE add_seqE.

Canonical Structure seq_czType :=
  Eval hnf in CZmodType {poly R} (seq CR) seq_czMixin.

Lemma trans_poly_def (p : {poly R}) : trans p = [seq trans x |  x <- p].
Proof. by []. Qed.

(* Subtraction *)
Definition sub_seq p q := add_seq p (opp_seq q).

Lemma sub_seqE : {morph trans : p q / p - q >-> sub_seq p q}.
Proof.
elim/poly_ind=> [q|p c IH q].
  by rewrite sub0r /sub_seq zeroE -opp_seqE /zero.
by rewrite /sub_seq -opp_seqE -add_seqE.
Qed.

(* lead_coef *)
Definition lead_coef_seq p := nth (zero CR) p (size p).-1.

Lemma lead_coef_seqE p : trans (lead_coef p) = lead_coef_seq (trans p).
Proof.
rewrite /lead_coef_seq /lead_coef trans_poly_def size_trans_poly /=.
remember (size p).-1; rewrite -Heqn; clear Heqn.
case: p => xs /= _.
by elim: n xs => [[] //=|n ih [] //=]; rewrite zeroE.
Qed.


(* Indeterminates *)
Definition indet n := ncons n (zero CR) [:: one CR].

Lemma indetE n : trans 'X^n = indet n.
Proof.
rewrite -['X^n]mul1r trans_poly_def polyseqMXn /indet ?oner_neq0
        // -zeroE -oneE.
by elim : n => //= [ | n -> ] //; rewrite polyseq1.
Qed.

(* polyC *)
Definition polyC_seq x := nseq (x != zero CR) x.

Lemma polyC_seqE x : trans (polyC x) = polyC_seq (trans x).
Proof.
rewrite trans_poly_def polyseqC /polyC_seq trans_eq0.
by case x0: (x == 0).
Qed.

(* Scaling *)
Fixpoint scale_seq x p := match p with
  | [::] => [::]
  | hd :: tl => let r   := scale_seq x tl in
                let xhd := mul x hd in
                if xhd == zero CR
                   then if r == [::] then [::] else xhd :: r
                   else xhd :: r
  end.

Lemma scale_seqE x : forall p,
  trans (scale_poly x p) = scale_seq (trans x) (trans p).
Proof.
elim/poly_ind=> [| p c IH]; first by rewrite scale_polyE mulr0 zeroE.
rewrite -cons_poly_def !trans_poly_def polyseq_cons.
case: ifP=> sp /=; last first.
  have p0: (p == 0) by move/negbT: sp; rewrite negbK nil_poly.
  rewrite cons_poly_def (eqP p0) mul0r add0r !polyseqC scale_polyE -polyC_mul.
  case c0: (c == 0)=> /=; first by rewrite (eqP c0) mulr0 polyseq0.
  rewrite -mulE trans_eq0.
  case: ifP=> xc0 /=; first by rewrite (eqP xc0) polyseq0.
  by rewrite polyseqC xc0.
rewrite -IH cons_poly_def !scale_polyE mulrDr -polyC_mul mulrA -mulE
        trans_eq0.
case: ifP=> xc0.
  rewrite (eqP xc0) addr0 trans_eq0.
  case: ifP; first by move/eqP=> ->; rewrite mul0r polyseq0.
  by move=> xpnil; rewrite polyseqMX // negbT.
rewrite  -cons_poly_def -scale_polyE polyseq_cons.
case: ifP=> // /negbT; rewrite negbK nil_poly=> /eqP ->.
by rewrite zeroE /zero /= polyseqC xc0.
Qed.

(* It is quite inefficient to compute mul_seq p (indet n) in order to
compute p * 'X^n. Instead this can be done by shifiting *)

Definition shift n p := if p == [::] then [::] else nseq n (zero CR) ++ p.

(* Why is this not in the library? *)
Lemma lead_coef_mulXn (p : {poly R}) : forall n, lead_coef (p * 'X^n) = lead_coef p.
Proof.
elim=> [|n ih]; first by rewrite expr0 mulr1.
by rewrite -addn1 exprD mulrA lead_coefMX.
Qed.

Lemma shiftE : forall n p, trans (p * 'X^n) = shift n (trans p).
Proof.
rewrite /shift.
elim=> [|n ih] p.
  rewrite expr0 /= mulr1.
  by case: ifP=> // /eqP ->.
case: ifP=> [|hf] /=.
  rewrite trans_poly_eq0 => /eqP ->.
  by rewrite mul0r zeroE.
move: (ih p).
rewrite hf -add1n addnC exprD expr1 mulrA !trans_poly_def polyseqMX /=.
  by rewrite zeroE => <-.
apply/negP.
rewrite -lead_coef_eq0 lead_coef_mulXn lead_coef_eq0 => /eqP hp.
by move: hf; rewrite hp zeroE eqxx.
Qed.


(* Multiplication *)
Fixpoint mul_seq p q := match p,q with
  | [::], _ => [::]
  | _, [::] => [::]
  | x :: xs,_ => add_seq (scale_seq x q) (mul_seq xs (shift 1 q))
  end.

Lemma mul_seqr0 : forall p, mul_seq p [::] = [::].
Proof. by case. Qed.

Lemma mul_seqE : {morph trans : p q / p * q >-> mul_seq p q}.
Proof.
elim/poly_ind=> [|p c IH] q; first by rewrite mul0r zeroE /zero.
case q0: (q == 0); first by rewrite (eqP q0) mulr0 zeroE /zero mul_seqr0.
rewrite !trans_poly_def -!cons_poly_def polyseq_cons.
elim/poly_ind: q q0=> [|q d _ /eqP /eqP q0]; first by rewrite eqxx.
rewrite /nilp.
case sp: (size p == 0%N) => /=.
  rewrite size_poly_eq0 in sp; rewrite (eqP sp) polyseqC.
  case c0: (c == 0).
    by rewrite (eqP c0) cons_poly_def mul0r add0r mul0r polyseq0.
  rewrite /= -scale_seqE -cons_poly_def polyseq_cons cons_poly_def.
  case: ifP=> [sq|].
    by rewrite scale_polyE -trans_poly0 -add_seqE addr0 mul0r add0r.
  rewrite size_poly_neq0 => /eqP; rewrite -polyseq0 => /poly_inj ->.
  rewrite polyseqC.
  case d0: (d == 0).
    by rewrite (eqP d0) !cons_poly_def mul0r !add0r mulr0 /= polyseq0.
  by rewrite !cons_poly_def scale_polyE mul0r !add0r add_seqr0.
rewrite -shiftE expr1 -IH.
rewrite -scale_seqE -cons_poly_def polyseq_cons /=.
case: ifP => /= sq0.
  by rewrite !cons_poly_def scale_polyE -add_seqE !mulrDl -!mulrA addrC
             !mulrDr [d%:P * 'X]mulrC ['X * (q * 'X)]mulrCA.
rewrite polyseqC.
move: sq0.
rewrite /nilp size_poly_eq0 => /eqP ->.
case d0: (d == 0) => /=.
  by rewrite (eqP d0) !cons_poly_def mul0r addr0 mulr0 polyseq0.
by rewrite scale_polyE -add_seqE !cons_poly_def mul0r add0r addrC mulrDl
           [d%:P * _]mulrC mulrA.
Qed.

(* CRING structure *)
Definition seq_cringMixin := CRingMixin trans_poly1 mul_seqE.

Canonical Structure seq_cringType :=
  Eval hnf in CRingType {poly R} seq_cringMixin.


(* Pseudo-division *)
Definition edivp_rec_seq (q : seq CR) :=
  let sq := size q in
  let cq := lead_coef_seq q in
  fix loop (n : nat) (k : nat) (qq r : seq CR) {struct n} :=
    if size r < sq then (k, qq, r) else
    let m := mul_seq (polyC_seq (lead_coef_seq r)) (indet (size r - sq)) in
    let qq1 := add_seq (mul_seq qq (polyC_seq cq)) m in
    let r1 := sub_seq (mul_seq r (polyC_seq cq)) (mul_seq m q) in
    if n is n1.+1 then loop n1 k.+1 qq1 r1 else (k.+1, qq1, r1).

Definition edivp_seq (p q : seq CR) : nat * seq CR * seq CR :=
  if q == [::] then (0%N, [::], p) else edivp_rec_seq q (size p) 0 [::] p.

Definition divp_seq p q := ((edivp_seq p q).1).2.
Definition modp_seq p q := (edivp_seq p q).2.
Definition scalp_seq p q := ((edivp_seq p q).1).1.

Lemma edivp_rec_seqE : forall n k (q qq r : {poly R}),
   let: (l,a,b) := redivp_rec q k qq r n
   in edivp_rec_seq (trans q) n k (trans qq) (trans r) = (l,trans a,trans b).
Proof.
elim=> [|n ih] k q qq r /=.
  case: ifP => // h; rewrite !size_trans_poly h //.
  by rewrite -indetE -!lead_coef_seqE -!polyC_seqE -!mul_seqE -add_seqE
             -sub_seqE mul_polyC.
case: ifP => // h; rewrite !size_trans_poly h //.
rewrite -indetE -!lead_coef_seqE -!polyC_seqE -!mul_seqE -add_seqE
  -sub_seqE mul_polyC.
exact: ih.
Qed.

Lemma edivp_seqE p q :
  let: (l,a,b) := redivp p q
  in edivp_seq (trans p) (trans q) = (l,trans a,trans b).
Proof.
rewrite /redivp unlock /redivp_expanded_def.
rewrite /edivp_seq trans_eq0 -trans_poly0 size_trans_poly.
by case: ifP => _ //=; apply: edivp_rec_seqE.
Qed.

Lemma divp_seqE : {morph trans : p q / rdivp p q >-> divp_seq p q}.
Proof.
rewrite /divp_seq /rdivp /= => p q.
move: (edivp_seqE p q).
by case: redivp=> [[a b c]] ->.
Qed.

Lemma modp_seqE : {morph trans : p q / rmodp p q >-> modp_seq p q}.
Proof.
rewrite /modp_seq /rmodp /= => p q.
move: (edivp_seqE p q).
by case: redivp=> [[a b c]] ->.
Qed.

Lemma scalp_seqE : forall p q, rscalp p q = scalp_seq (trans p) (trans q).
Proof.
rewrite /scalp_seq /rscalp /= => p q.
move: (edivp_seqE p q).
by case: redivp=> [[a b c]] ->.
Qed.


(* Horner evaluation *)

Fixpoint horner_seq s x :=
  if s is a :: s' then add (mul (horner_seq s' x) x) a else zero CR.

Lemma horner_seqE : forall p x, trans p.[x] = horner_seq (trans p) (trans x).
Proof.
elim/poly_ind => [ x | p c]; first by rewrite horner0 !zeroE.
rewrite /horner_seq -!cons_poly_def !trans_poly_def polyseq_cons /nilp => ih x.
case sp0: (size p == 0%N) => /=.
  move: sp0; rewrite size_poly_eq0 => /eqP ->.
  rewrite horner_cons polyseqC horner0 mul0r add0r.
  case c0: (c == 0) => /=; first by rewrite (eqP c0) zeroE.
  by rewrite -zeroE -mulE mul0r -addE add0r.
by rewrite -ih -mulE -addE horner_cons.
Qed.

End SeqPoly.