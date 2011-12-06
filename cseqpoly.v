Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg poly.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Require Import cssralg.

Section SeqPoly.

Variable R : comRingType.
Variable CR : cringType R.

Definition trans_poly (p : {poly R}) : seq CR := map (@trans R CR) (polyseq p).

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
Proof. by rewrite /trans_poly seq_poly0. Qed.

Lemma trans_poly1 : trans_poly 1 = [:: (one CR)].
Proof. by rewrite /trans_poly polyseq1 -oneE. Qed.

Lemma trans_poly_eq0 : forall p, (trans_poly p == [::]) = (p == 0).
Proof.
move=> p.
apply/eqP/eqP=> [h|->].
  apply/inj_trans_poly.
  by rewrite h trans_poly0.
by rewrite trans_poly0.
Qed.

Lemma size_trans_poly : forall (p : {poly R}), size (trans_poly p) = size p.
Proof.
rewrite /trans_poly.
elim=> xs /= _.
by elim: xs => //= x xs ->.
Qed.

(* Reflection lemma *)
Lemma trans_polyP : forall p q : {poly R},
  reflect (p = q) (trans_poly p == trans_poly q).
Proof.
move=> p q.
apply: (iffP idP)=> [|->] // /eqP.
exact: (@inj_trans_poly p q).
Qed.

(* Addition *)
Fixpoint add_seq p q : seq CR := match p, q with
  | [::], _ => q
  | _, [::] => p
  | x :: xs, y :: ys =>
        let xy := add x y in
        let r  := add_seq xs ys
        in if xy == (@zero R CR) then if r == [::] then [::] else xy :: r else xy :: r
  end.

Lemma add_seqr0 : forall p, add_seq p [::] = p.
Proof. by case. Qed.

Lemma poly_cons_add : forall (x y : R) (xs ys : {poly R}),
  poly_cons x xs + poly_cons y ys = poly_cons (x + y) (xs + ys).
Proof.
move=> x y xs ys.
by rewrite !poly_cons_def mulr_addl addrCA polyC_add -!addrA addrCA.
Qed.

Lemma size_poly_neq0 : forall (p: {poly R}),
  (size p != 0%N) = (p != [::] :> seq R).
Proof.
by move => p; rewrite (size_poly_eq0 p) -seq_poly0.
Qed.

Lemma add_seqE : {morph trans_poly : p q / p + q >-> add_seq p q}.
Proof.
rewrite /trans_poly.
elim/poly_ind=> [q| p c IH q].
  by rewrite add0r seq_poly0.
elim/poly_ind: q => [| q d _] .
  by rewrite addr0 seq_poly0 add_seqr0.
rewrite -!poly_cons_def poly_cons_add !polyseq_cons.
case: ifP => [|spq].
  case: ifP => sp.
    case: ifP => sq.
      rewrite size_poly_neq0 /= -addE trans_eq0.
      case: ifP; rewrite -IH //.
      move: (trans_poly_eq0 (p + q)).
      rewrite /trans_poly -seq_poly0 => ->.
      by case: ifP=> // /eqP ->; rewrite eqxx.
    rewrite polyseqC.
    have q0: (q == 0) by move/eqP: sq => /eqP; rewrite size_poly_eq0.
    case d0: (d == 0)=> /=; first by rewrite (eqP d0) (eqP q0) !addr0.
    rewrite -addE trans_eq0.
    rewrite (eqP q0) addr0 add_seqr0 size_poly_neq0 => /negbTE.
    move: (trans_poly_eq0 p).
    rewrite /trans_poly -seq_poly0 => ->.
    do 2! case: ifP => //.
    by move/eqP->; rewrite eqxx.
  have p0: (p == 0) by move/eqP: sp=> /eqP; rewrite size_poly_eq0.
  rewrite (eqP p0) !add0r polyseqC=> H.
  rewrite H; rewrite size_poly_neq0 in H.
  case c0: (c == 0)=> /=; first by rewrite (eqP c0) add0r.
  move: H.
  rewrite -addE trans_eq0.
  move: (trans_poly_eq0 q).
  rewrite /trans_poly -seq_poly0 => ->.
  do 2! case: ifP => //.
  by move/eqP->; rewrite eqxx.
move/eqP: spq => /eqP.
rewrite size_poly_eq0 addrC addr_eq0=> /eqP ->.
rewrite size_opp !polyseqC.
case: ifP=> h /=.
  by rewrite -IH subrr seq_poly0 /= -addE trans_eq0; case: ifP.
case c0: (c == 0)=> /=; first by rewrite (eqP c0) add0r.
case d0: (d == 0)=> /=; first by rewrite (eqP d0) addr0 (negbT c0) /=.
by rewrite -addE trans_eq0; case: ifP.
Qed.

(* Negation *)
Definition opp_seq p : seq CR := map (fun x => opp x) p.

Lemma opp_poly_cons : forall (c : R) p, -(poly_cons c p) = poly_cons (-c) (-p).
Proof.
move=> c p.
rewrite !poly_cons_def.
apply/polyP=> i.
rewrite coef_opp_poly !coef_add_poly !coef_mulX.
case: i=> [|n].
  by rewrite eqxx !add0r polyC_opp coef_opp.
by rewrite coef_opp polyC_opp coef_opp oppr_add.
Qed.

Lemma opp_seqE : {morph trans_poly : p / - p >-> opp_seq p }.
Proof.
rewrite /trans_poly.
elim/poly_ind=> [|p c IH].
  by rewrite oppr0 seq_poly0.
rewrite -!poly_cons_def opp_poly_cons !polyseq_cons size_opp.
case: ifP=> sp /=; first by rewrite -IH oppE.
by rewrite !polyseqC oppr_eq0; case: (c == 0) => //=; rewrite oppE.
Qed.

(* CZmodule structure *)
Definition seq_czMixin := @CZmodMixin
  [zmodType of {poly R}] (seq CR) [::]
  opp_seq add_seq poly_trans_struct trans_poly0 opp_seqE add_seqE.

Canonical Structure seq_czType :=
  Eval hnf in CZmodType {poly R} (seq CR) seq_czMixin.

(* Subtraction *)
Definition sub_seq p q : seq CR := add_seq p (opp_seq q).

Lemma sub_seqE : {morph trans_poly : p q / p - q >-> sub_seq p q}.
Proof.
elim/poly_ind=> [q|p c IH q].
  by rewrite sub0r /sub_seq trans_poly0 /= opp_seqE.
by rewrite /sub_seq -opp_seqE -add_seqE.
Qed.

(* lead_coef *)
Definition lead_coef_seq (p : seq CR) := nth (@zero R CR) p (size p).-1.

Lemma lead_coef_seqE : forall p, trans CR (lead_coef p) = lead_coef_seq (trans_poly p).
Proof.
move=> p.
rewrite /lead_coef_seq /lead_coef size_trans_poly /trans_poly /=.
remember (size p).-1; rewrite -Heqn; clear Heqn.
elim: p => xs /= _.
by elim: n xs => [[] //=|n ih [] //=]; rewrite zeroE.
Qed.

(* Indeterminates *)
Definition indet (n : nat) : seq CR := ncons n (@zero R CR) [:: (@one R CR)].

Lemma indetE : forall n, trans_poly 'X^n = indet n.
Proof.
move=> n.
rewrite /trans_poly seq_polyXn /indet -zeroE -oneE.
by elim: n => //= n ->.
Qed.

(* polyC *)
Definition polyC_seq x : seq CR := nseq (x != (@zero R CR)) x.

Lemma polyC_seqE : forall x, trans_poly (polyC x) = polyC_seq (trans CR x).
Proof.
move=> x.
rewrite /trans_poly polyseqC /polyC_seq trans_eq0.
by case x0: (x == 0).
Qed.

(* Scaling *)
Fixpoint scale_seq x p : seq CR := match p with
  | [::] => [::]
  | hd :: tl => let r   := scale_seq x tl in
                let xhd := mul x hd in
                if xhd == (@zero R CR)
                   then if r == [::] then [::] else xhd :: r
                   else xhd :: r
  end.

Lemma scale_seqE : forall (x : R) (p : {poly R}),
  trans_poly (scale_poly x p) = scale_seq (trans CR x) (trans_poly p).
Proof.
move=> x.
elim/poly_ind=> [| p c IH].
  by rewrite scale_polyE mulr0 trans_poly0.
rewrite -poly_cons_def /trans_poly polyseq_cons.
case: ifP=> sp /=; last first.
  have p0: (p == 0) by move/eqP: sp; move/eqP; rewrite size_poly_eq0.
  rewrite poly_cons_def (eqP p0) mul0r add0r !polyseqC scale_polyE -polyC_mul.
  case c0: (c == 0)=> /=; first by rewrite (eqP c0) mulr0 seq_poly0.
  rewrite -mulE trans_eq0.
  case: ifP=> xc0 /=; first by rewrite (eqP xc0) seq_poly0.
  by rewrite polyseqC xc0.
rewrite -IH poly_cons_def !scale_polyE mulr_addr -polyC_mul mulrA -mulE
        trans_eq0.
case: ifP=> xc0.
  rewrite (eqP xc0) addr0 trans_poly_eq0.
  case: ifP; first by move/eqP=> ->; rewrite mul0r seq_poly0.
  by move=> xpnil; rewrite seq_mul_polyX // negbT.
rewrite -poly_cons_def -scale_polyE polyseq_cons.
case: ifP=> // /eqP /eqP; rewrite size_poly_eq0=> /eqP ->.
by rewrite polyseqC xc0 trans_poly0.
Qed.

(* It is quite inefficient to compute mul_seq p (indet n) in order to
compute p * 'X^n. Instead this can be done by shifiting *)

Definition shift (n : nat) (p : seq CR) :=
  if p == [::] then [::] else nseq n (@zero R CR) ++ p.

(* Why is this not in the library? *)
Lemma lead_coef_mulXn : forall (p : {poly R}) (n : nat), lead_coef (p * 'X^n) = lead_coef p.
Proof.
move=> p.
elim=> [|n ih]; first by rewrite expr0 mulr1.
by rewrite -addn1 exprn_addr mulrA lead_coef_mulX.
Qed.

Lemma shiftE : forall n p, trans_poly (p * 'X^n) = shift n (trans_poly p).
Proof.
rewrite /shift.
elim=> [|n ih] p.
  rewrite expr0 /= mulr1.
  by case: ifP=> // /eqP ->.
case: ifP=> [|hf] /=.
  rewrite trans_poly_eq0 => /eqP ->.
  by rewrite mul0r trans_poly0.
move: (ih p).
rewrite hf -add1n addnC exprn_addr expr1 mulrA /trans_poly seq_mul_polyX /=.
  by rewrite zeroE => <-.
apply/negP.
rewrite -lead_coef_eq0 lead_coef_mulXn lead_coef_eq0 => /eqP hp.
by move: hf; rewrite hp trans_poly0 eqxx.
Qed.


(* Multiplication *)
Fixpoint mul_seq p q := match p,q with
  | [::], _ => [::]
  | _, [::] => [::]
  | x :: xs,_ => add_seq (scale_seq x q) (mul_seq xs (shift 1 q))
  end.

Lemma mul_seqr0 : forall p, mul_seq p [::] = [::].
Proof. by case. Qed.

Lemma mul_seqE : {morph trans_poly : p q / p * q >-> mul_seq p q}.
Proof.
rewrite /trans_poly.
elim/poly_ind=> [|p c IH] q; first by rewrite mul0r seq_poly0.
case q0: (q == 0); first by rewrite (eqP q0) mulr0 seq_poly0 mul_seqr0.
rewrite -!poly_cons_def polyseq_cons.
elim/poly_ind: q q0=> [|q d _ /eqP /eqP q0]; first by rewrite eqxx.
case sp: (size p == 0%N) => /=.
  rewrite size_poly_eq0 in sp; rewrite (eqP sp) polyseqC.
  case c0: (c == 0).
    by rewrite (eqP c0) poly_cons_def mul0r add0r mul0r seq_poly0.
  rewrite /= -scale_seqE -poly_cons_def polyseq_cons poly_cons_def.
  case: ifP=> [sq|].
    by rewrite scale_polyE -trans_poly0 -add_seqE addr0 mul0r add0r.
  rewrite size_poly_neq0 => /eqP; rewrite -seq_poly0 => /poly_inj ->.
  rewrite polyseqC.
  case d0: (d == 0).
    by rewrite (eqP d0) !poly_cons_def mul0r !add0r mulr0 /= seq_poly0.
  by rewrite /trans_poly !poly_cons_def scale_polyE mul0r !add0r add_seqr0.
rewrite -shiftE expr1 -IH.
rewrite -scale_seqE -poly_cons_def polyseq_cons /=.
case: ifP => /= sq0.
  rewrite !poly_cons_def scale_polyE -add_seqE /trans_poly.
  rewrite !mulr_addl -!mulrA addrC.
  rewrite !mulr_addr.
  by rewrite [d%:P * 'X]mulrC ['X * (q * 'X)]mulrCA.
rewrite polyseqC.
move: sq0.
rewrite size_poly_eq0 => /eqP ->.
case d0: (d == 0) => /=.
  by rewrite (eqP d0) !poly_cons_def mul0r addr0 mulr0 seq_poly0.
rewrite scale_polyE -add_seqE !poly_cons_def mul0r add0r /trans_poly addrC.
rewrite mulr_addl.
by rewrite [d%:P * _]mulrC mulrA.
Qed.

(* CRING structure *)
Definition seq_cringMixin := CRingMixin trans_poly1 mul_seqE.

Canonical Structure seq_cringType :=
  Eval hnf in CRingType {poly R} seq_cringMixin.


(* Pseudo-division *)
Definition edivp_rec_seq (q : seq CR)  :=
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

Lemma edivp_rec_seqE :
 forall n k (q qq r : {poly R}),
   let: (l,a,b) := edivp_rec q n k qq r
   in edivp_rec_seq (trans_poly q) n k (trans_poly qq) (trans_poly r) =
      (l,trans_poly a,trans_poly b).
Proof.
elim=> [|n ih] k q qq r /=.
  case: ifP => // h; rewrite !size_trans_poly h //.
  by rewrite -indetE -!lead_coef_seqE -!polyC_seqE -!mul_seqE -add_seqE
             -sub_seqE.
case: ifP => // h; rewrite !size_trans_poly h //.
rewrite -indetE -!lead_coef_seqE -!polyC_seqE -!mul_seqE -add_seqE -sub_seqE.
exact: ih.
Qed.

Lemma edivp_seqE :
  forall p q,
    let: (l,a,b) := edivp p q
    in edivp_seq (trans_poly p) (trans_poly q) = (l,trans_poly a,trans_poly b).
Proof.
rewrite /edivp /edivp_seq=> p q.
rewrite trans_poly_eq0 -trans_poly0 size_trans_poly.
case: ifP => _; first by rewrite trans_poly0.
exact: edivp_rec_seqE.
Qed.

Lemma divp_seqE : {morph trans_poly : p q / divp p q >-> divp_seq p q}.
Proof.
rewrite /divp_seq /divp /= => p q.
move: (edivp_seqE p q).
by case: edivp=> [[a b c]] ->.
Qed.

Lemma modp_seqE : {morph trans_poly : p q / modp p q >-> modp_seq p q}.
Proof.
rewrite /modp_seq /modp /= => p q.
move: (edivp_seqE p q).
by case: edivp=> [[a b c]] ->.
Qed.

Lemma scalp_seqE : forall p q, scalp p q = scalp_seq (trans_poly p) (trans_poly q).
Proof.
rewrite /scalp_seq /scalp /= => p q.
move: (edivp_seqE p q).
by case: edivp=> [[a b c]] ->.
Qed.


(* Horner evaluation *)

Fixpoint horner_seq (s : seq CR) (x : CR) {struct s} : CR :=
  if s is a :: s' then add (mul (horner_seq s' x) x) a else zero CR.

Lemma horner_seqE : forall p x,
  trans CR (polyseq p).[x] = horner_seq (trans_poly p) (trans CR x).
Proof.
elim/poly_ind => [ x | p c]; first by rewrite horner0 trans_poly0 zeroE.
rewrite /horner_seq -!poly_cons_def /trans_poly polyseq_cons => ih x.
case sp0: (size p == 0%N) => /=.
  rewrite hornerC polyseqC.
  case c0: (c == 0) => /=; first by rewrite (eqP c0) zeroE.
  by rewrite -zeroE -mulE mul0r -addE add0r.
by rewrite -ih -mulE -addE.
Qed.

End SeqPoly.