Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div fintype tuple.
Require Import finfun bigop fingroup perm ssralg zmodp matrix mxalgebra.
Require Import poly polydiv mxpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Import GRing.Theory.

Open Scope ring_scope.

Section split_poly.

Variable R : ringType.

Implicit Types p : {poly R}.

(* Split a polynomial into n pieces of size b *)
Definition split_poly n b p := 
  \poly_(i < n) \poly_(j < b) p`_(i * b + j).

Lemma recompose_split : forall n b p, size p <= b * n ->
  (split_poly n b p).['X^b] = p.
Proof.
rewrite /split_poly => [[b p|n b p hs]]; rewrite horner_poly ?big_ord_recr /=.
  by rewrite muln0 leqn0 size_poly_eq0 => /eqP ->; rewrite big_ord0.
suff -> : \big[+%R/0]_(i < n) (\poly_(j < b) p`_(i * b + j) * 'X^b ^+ i) = 
          \poly_(i < n * b) p`_i.
  apply/polyP=> i; rewrite -exprM coefD coefMXn coef_poly mulnC.
  have [_|hbni] := ltnP; rewrite ?addr0 // add0r coef_poly.
  have [_|hsub] := ltnP; rewrite ?subnKC // ?nth_default //.
  rewrite -ltnS -subSn // ltn_subRL ltnS addnC -mulnS in hsub.
  exact: (leq_trans hs hsub).
elim: n {hs} => [|n ih]; first by rewrite mul0n poly_def !big_ord0.
apply/polyP=> i. 
rewrite big_ord_recr /= ih -exprM coefD !coef_poly coefMXn mulSn mulnC.
have [h1|hbni] := ltnP; first by rewrite addr0 (ltn_addl b h1).
by rewrite add0r coef_poly subnKC // -(ltn_add2r (b * n)) subnK.
Qed.

End split_poly.

Section ToomCook.

(* Necessary to interpolate... *)
Variable R : idomainType.

(* Toom-n *)
Variable n : nat.

(* Need d = 2 * n - 1 pairs of points *)
Let d : nat := n.*2.-1.

Variable points : d.-tuple {poly R}.

(* Vandermonde matrix *)
Definition vandmx m : 'M[{poly R}]_(m,d) :=
  \matrix_(i < m,j < d) (points`_j ^+ i).

(* Evaluation *)
Definition evaluate p := poly_rV p *m vandmx (size p).

Lemma evaluateE p : evaluate p = \row_(i < d) p.[points`_i].
Proof. 
apply/rowP => i; rewrite !mxE horner_coef /=.
by apply: eq_big => // j _; rewrite !mxE.
Qed.

(* Interpolation *)
Definition interpolate (p : 'rV[{poly R}]_d) := rVpoly (p *m invmx (vandmx d)).

(* TODO: Express using determinant? *)
Hypothesis hU : vandmx d \in unitmx.

Lemma interpolateE (p : {poly {poly R}}) : size p <= d -> 
  interpolate (\row_i p.[points`_i]) = p.
Proof.
rewrite /interpolate => hsp; rewrite -[RHS](poly_rV_K hsp); congr rVpoly.
apply/(canLR (mulmxK hU))/rowP=> i; rewrite !mxE (horner_coef_wide _ hsp). 
by apply: eq_bigr=> j _ ; rewrite !mxE.
Qed.

Fixpoint toom_rec m p q : {poly R} := match m with
  | 0 => p * q
  | m'.+1 => (* if (size p <= 2) || (size q <= 2) then p * q else *)
    let: b  := (maxn (divn (size p) n) (divn (size q) n)).+1 in
    let: sp := split_poly n b p in
    let: sq := split_poly n b q in
    let: ep := evaluate sp in
    let: eq := evaluate sq in
    let: r  := \row_i (toom_rec m' (ep 0 i) (eq 0 i)) in
    let: w  := interpolate r in
    w.['X^b]
  end.

Definition toom_cook (p q : {poly R}) :=
  if 0 < n then toom_rec (maxn (size p) (size q)) p q else p * q.

Lemma basisE (p q : {poly R}) : 0 < n -> 
  size p <= (maxn (size p %/ n) (size q %/ n)).+1 * n.
Proof.
move=> Hn0; move: (leq_maxl (size p %/ n).+1 (size q %/ n).+1). 
by rewrite -(leq_pmul2r Hn0) maxnSS; apply/leq_trans/ltnW; rewrite ltn_ceil.
Qed.

Lemma toom_recE (Hn0 : 0 < n) : forall m p q, toom_rec m p q = p * q.
Proof.
elim=> //= m ih p q. (* ; case: ifP=> // h. *)
set sp := split_poly _ _ p; set sq := split_poly _ _ q.
set ep := evaluate sp; set eq := evaluate sq.
have hspq : size (sp * sq) <= d.
  rewrite (leq_trans (size_mul_leq _ _)) // /d -!subn1 leq_sub2r // -addnn.
  by apply/leq_add; rewrite size_poly.
have -> : \row_i toom_rec m (ep 0 i) (eq 0 i) = \row_i (sp * sq).[points`_i].
  by apply/rowP=> i; rewrite mxE ih /ep /eq !evaluateE !mxE hornerM.
by rewrite (interpolateE hspq) hornerM !recompose_split ?basisE // maxnC basisE.
Qed.

Lemma toom_cookE p q : toom_cook p q = p * q.
Proof. rewrite /toom_cook; case: (ltnP 0 n)=> // hn0; exact: toom_recE. Qed.

End ToomCook.