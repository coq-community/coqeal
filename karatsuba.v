Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg poly.
Require Import bigop cseqpoly cssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Section karatsuba.

Variable R : comRingType.
Variable CR : cringType R.

Implicit Types p q : {poly R}.

(* Splitting polynomials *)

Definition splitp n p := (Poly (drop n p), Poly (take n p)).

Lemma coef_oversize : forall p i, size p <= i -> p`_i = 0.
Proof.
elim/poly_ind => [i | p c ih i]; first by rewrite coef0.
case i0: (i == 0%N).
  move/eqP: i0 => ->.
  rewrite leqn0 size_poly_eq0 => /eqP ->.
  by rewrite coef0.
rewrite -poly_cons_def size_poly_cons coef_cons=> h.
rewrite i0 ih //.
move: h.
case: ifP => [|_ spi].
  by case/andP=> /eqP ->; rewrite !leq0n.
by rewrite -ltnS (prednK (neq0_lt0n i0)).
Qed.

Lemma splitP : forall n p, p = (splitp n p).1 * 'X^n + (splitp n p).2.
Proof.
move=> n p /=.
apply/polyP=> i.
rewrite coefD coefMXn.
case: ifP => hin.
  by rewrite coef_Poly add0r nth_take.
rewrite {1}coef_Poly nth_drop addnC subnK; last first.
  by rewrite leqNgt hin.
move/negP: hin => /negP.
rewrite -leqNgt=> h.
case: (ltnP n (size p)) => sh.
  have size_take: (size (Poly (take n p)) <= i).
    move: (size_Poly (take n p)).
    move: (size_take n p).
    rewrite sh => -> h1.
    by rewrite (leq_trans h1).
  by rewrite (@coef_oversize (Poly (take n p))) // addr0.
by rewrite coef_Poly take_oversize // coef_oversize ?addr0 // (leq_trans sh).
Qed.

(* Karatsuba multiplication *)



(* Karatsuba multiplication *)
Fixpoint karatsuba_rec (n : nat) p q := match n with
  | 0%N   => p * q
  | n'.+1 => if (size p <= 2) || (size q <= 2) then p * q else
      let m       := minn (size p)./2 (size q)./2 in
      let (p1,p2) := splitp m p in
      let (q1,q2) := splitp m q in
      let p1q1    := karatsuba_rec n' p1 q1 in
      let p2q2    := karatsuba_rec n' p2 q2 in
      let p12     := p1 + p2 in
      let q12     := q1 + q2 in
      let p12q12  := karatsuba_rec n' p12 q12 in
      p1q1 * 'X^(2 * m) + (p12q12 - p1q1 - p2q2) * 'X^m + p2q2
  end.

Definition karatsuba p q :=
  let (p1,q1) := if size p < size q then (q,p) else (p,q) in
  karatsuba_rec (size p1) p1 q1.

Lemma karatsuba_recP : forall n p q, karatsuba_rec n p q = p * q.
Proof.
elim=> // n ih p q /=.
case: ifP=> // sp.
apply/eqP.
set m := minn (size p)./2 (size q)./2.
rewrite eq_sym {1}(splitP m p) {1}(splitP m q) /=.
rewrite !ih; do ?(by rewrite ?hm ?doubleK).
set p1 := (Poly (drop m p)).
set p2 := (Poly (take m p)).
set q1 := (Poly (drop m q)).
set q2 := (Poly (take m q)).
rewrite !mulr_addl !mulr_addr -!mulrA ['X^m * (_ * _)]mulrCA -exprn_addr addnn
        -mul2n.
apply/eqP.
rewrite -!addrA.
congr (_ + _).
rewrite mulr_addl -!mulrA [p1 * _+ p1 * _]addrC ['X^m * q2]mulrC -!addrA.
congr (_ + _).
rewrite mulr_addl -!addrA addrCA -!mulrA.
congr (_ + _).
rewrite !addrA -{1}[p2*q2]add0r.
congr (_ + _).
apply/eqP.
rewrite eq_sym addr_eq0 -addrA addrCA addrC -addrA eq_sym addrC -subr_eq.
by rewrite -!mulrN -!mulrA mulrNN mulrN mulNr addrC.
Qed.


Lemma karatsubaP : forall p q, karatsuba p q = p * q.
Proof.
move=> p q.
rewrite /karatsuba.
wlog sqp : p q / size q <= size p=> [H|].
  case: ltnP=> spq.
    by move/H: (ltnW spq); rewrite ltnNge (ltnW spq) mulrC.
  by move/H: (spq); rewrite ltnNge spq.
by rewrite ltnNge sqp /= karatsuba_recP.
Qed.


(* seq version *)

(* This is written to reflect Poly *)
Fixpoint take' n (s : seq CR) :=  match n, s with
  | n'.+1, x :: s' => let r := take' n' s'
                      in if size r != 0%N then x :: r else nseq (x != zero CR) x
  | _, _ => [::]
  end.


Lemma last_drop : forall (p : seq R) n, last 1 p != 0 -> last 1 (drop n p) != 0.
Proof.
elim => /= [| x xs ih n h]; first by rewrite nonzero1r.
case: n ih => // n -> //.
case: xs h => //=.
by rewrite nonzero1r.
Qed.

Definition splitp_seq n (p : seq CR) := (drop n p, take' n p).

Lemma splitp_seqE : forall p n,
  (trans_poly CR (splitp n p).1,trans_poly CR (splitp n p).2) =
  splitp_seq n (trans_poly CR p).
Proof.
rewrite /splitp_seq /= => p n.
apply/pair_eqP => /=.
apply/andP.
case: p => p /= h.
split; first by rewrite /trans_poly (@PolyK _ 1) ?map_drop // last_drop.
rewrite {2}/trans_poly /=.
apply/eqP; clear h.
elim: p n => [[]|x xs ih n] /=; try by rewrite trans_poly0.
case: n => [|n] /=; first by rewrite trans_poly0.
rewrite trans_eq0 -ih size_trans_poly /trans_poly polyseq_cons polyseqC.
case: ifP => //= _.
by case: (x == 0).
Qed.

Fixpoint karatsuba_rec_seq (n : nat) (p q : seq CR) := match n with
  | 0%N   => mul_seq p q
  | n'.+1 => if (size p <= 2) || (size q <= 2) then mul_seq p q else
      let m       := minn (size p)./2 (size q)./2 in
      let (p1,p2) := splitp_seq m p in
      let (q1,q2) := splitp_seq m q in
      let p1q1    := karatsuba_rec_seq n' p1 q1 in
      let p2q2    := karatsuba_rec_seq n' p2 q2 in
      let p12     := add_seq p1 p2 in
      let q12     := add_seq q1 q2 in
      let p12q12  := karatsuba_rec_seq n' p12 q12 in
      add_seq (add_seq (shift (2 * m) p1q1)
              (shift m (sub_seq (sub_seq p12q12 p1q1) p2q2))) p2q2
  end.

Definition karatsuba_seq (p q : seq CR) :=
  let (p1,q1) := if size p < size q then (q,p) else (p,q) in
  karatsuba_rec_seq (size p1) p1 q1.

Lemma karatsuba_rec_seqE : forall n,
  {morph (trans_poly CR) : p q / karatsuba_rec n p q >-> karatsuba_rec_seq n p q}.
Proof.
elim=> /= [|n ih p q]; first exact: mul_seqE.
rewrite !size_trans_poly.
case: ifP=> _; first exact: mul_seqE.
set m := minn (size p)./2 (size q)./2.
case: (splitp_seqE p m) => <- <-.
case: (splitp_seqE q m) => <- <-.
by rewrite -!add_seqE -!ih -!sub_seqE -!shiftE -!add_seqE.
Qed.

Lemma karatsuba_seqE : {morph (trans_poly CR) : p q / karatsuba p q >-> karatsuba_seq p q}.
Proof.
move=> p q /=.
rewrite /karatsuba /karatsuba_seq !size_trans_poly.
by case: ifP=> _; rewrite karatsuba_rec_seqE !size_trans_poly.
Qed.

End karatsuba.
