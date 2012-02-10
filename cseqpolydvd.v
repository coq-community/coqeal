Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg poly.
Require Import dvdring cdvdring polydvd cseqpoly cssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Module CSeqPoly_dvd.
Section CSeqPoly_dvd.

(* This is seqpolydvd but with computable ring as base ring *)

(* Proof that seq CR is a ring with explicit divisibility *)
Variable R : dvdRingType.
Variable CR : cdvdRingType R.

Implicit Types p q : seq CR.

Definition odivp_rec_seq q :=
  let sq := size q in
  let lq := lead_coef_seq q in
  fix loop (n : nat) (r p : seq CR) {struct n} :=
    if p == [::] then Some r else
    if size p < sq then None else
    match cdiv (lead_coef_seq p) lq with
      | Some x => let m  := mul_seq (polyC_seq x) (indet CR (size p - sq)) in
                  let r1 := add_seq r m in
                  let p1 := sub_seq p (mul_seq m q) in
                  if n is n1.+1 then loop n1 r1 p1 else None
      | None   => None
    end.

Definition odivp_seq p q : option (seq CR) :=
  if p == [::] then Some [::] else odivp_rec_seq q (size p) [::] p.

Import PolyDvdRing.

Lemma odivp_recE :
 forall n (q r p : {poly R}),
  odivp_rec_seq (trans_poly CR q) n (trans_poly CR r) (trans_poly CR p) =
   omap (trans_poly CR) (odivp_rec q n r p).
Proof.
elim=> [q r p|n IH q r p] /=.
  rewrite trans_poly_eq0 !size_trans_poly -!lead_coef_seqE -cdivE.
  do 2! case: ifP => //.
  by case: odivrP.
rewrite trans_poly_eq0 !size_trans_poly -!lead_coef_seqE -cdivE.
do 2! case: ifP => //.
case: odivrP => // x hx /=.
by rewrite -IH -polyC_seqE -indetE -!mul_seqE add_seqE sub_seqE.
Qed.

Lemma odivp_seqE :
  forall p q : {poly R}, omap (trans_poly CR) (p %/? q) =
                         odivp_seq (trans_poly CR p) (trans_poly CR q).
Proof.
rewrite /odivr /= /odivp /odivp_seq => p q.
rewrite trans_poly_eq0.
case: ifP => hp /=; first by rewrite trans_poly0.
by rewrite size_trans_poly -trans_poly0 odivp_recE.
Qed.

(* CDvdring structure *)
Definition seq_cdvdRingMixin := CDvdRingMixin odivp_seqE.

Canonical Structure seq_cdvdRingType :=
  Eval hnf in CDvdRingType [dvdRingType of {poly R}] seq_cdvdRingMixin.

End CSeqPoly_dvd.
End CSeqPoly_dvd.


Module CSeqPoly_gcd.
Section CSeqPoly_gcd.

Import CSeqPoly_dvd.

(* GCD operations on cseqpoly *)
Variable R : gcdRingType.
Variable CR : cgcdRingType R.

Implicit Types p q : seq CR.

Definition gcdsr_seq := foldr (@cgcd R CR) (zero CR).

Lemma gcdsr_seqE : forall p : {poly R}, trans (@gcdsr R p) = gcdsr_seq (trans_poly CR p).
Proof.
move=> p.
rewrite /trans_poly.
elim: p => xs /= _.
elim: xs => [|x xs ih] /=; first by rewrite zeroE.
by rewrite -ih cgcdE.
Qed.

(* Primitive part *)
Definition pp_seq p : seq CR := match odivp_seq p (polyC_seq (gcdsr_seq p)) with
  | Some x => x
  | None   => [:: (one CR)]
  end.

Import PolyGcdRing.

Lemma pp_seqE : {morph (trans_poly CR) : p / pp p >-> pp_seq p}.
Proof.
move=> p /=.
rewrite /pp /pp_seq -gcdsr_seqE -polyC_seqE -odivp_seqE.
case: odivrP => //=.
by rewrite -oneE /trans_poly polyseq1.
Qed.

Fixpoint gcdp_rec_seq (n : nat) (p q : seq CR) :=
  let r := modp_seq p q in
  if r == [::]
     then q
     else if n is n'.+1 then gcdp_rec_seq n' q (pp_seq r) else pp_seq r.

Definition gcdp_seq (p q : seq CR) :=
  let (p1,q1) := if size p < size q then (q,p) else (p,q) in
  let d  := polyC_seq (cgcd (gcdsr_seq p1) (gcdsr_seq q1)) in
  mul_seq d (gcdp_rec_seq (size (pp_seq p1)) (pp_seq p1) (pp_seq q1)).

Lemma gcdp_rec_seqE :
 forall n (p q : {poly R}),
   gcdp_rec_seq n (trans_poly CR p) (trans_poly CR q) = trans_poly CR (gcdp_rec n p q).
Proof.
by elim=> [|n ih] p q /=; rewrite -modp_seqE trans_poly_eq0 -pp_seqE; case: ifP.
Qed.

Lemma gcdp_seqE : {morph (trans_poly CR) : p q / gcdp p q >-> gcdp_seq p q}.
Proof.
rewrite /gcdp /gcdp_seq => p q /=; rewrite !size_trans_poly.
by case: ifP;
   rewrite -!gcdsr_seqE -!pp_seqE -cgcdE -!polyC_seqE gcdp_rec_seqE -mul_seqE
           size_trans_poly.
Qed.

(* CGcdRing structure *)
Definition seq_cgcdRingMixin := CGcdRingMixin gcdp_seqE.

Canonical Structure seq_cgcdRingType :=
  Eval hnf in CGcdRingType [gcdRingType of {poly R}] seq_cgcdRingMixin.

End CSeqPoly_gcd.
End CSeqPoly_gcd.

Module KX.
Section KX.
(* Computational Euclidean ring structure on k[x] *)

(* This does not work as intended as we only can have one seq instance of
dvdring. So we can't iterate the construction for seq K to get multivariate gcd
over fields. *)

Variable K : fieldType.
Variable CK : cunitRingType K.

Implicit Types p q : seq CK.

Import PolyPriField.

(* Euclidean ring structure on k[x] *)
Definition ediv_rec_seq q :=
  let sq := size q in
  let lq := lead_coef_seq q in
  fix loop (n : nat) (qq r : seq CK) {struct n} :=
    if size r < sq then (qq, r) else
    let m := mul_seq (polyC_seq (cudiv (lead_coef_seq r) lq))
                     (indet CK (size r - sq)) in
    let qq1 := add_seq qq m in
    let r1 := sub_seq r (mul_seq m q) in
    if n is n1.+1 then loop n1 qq1 r1 else (qq1, r1).

Definition ediv_seq p q : seq CK * seq CK :=
  if q == [::] then ([::], p) else ediv_rec_seq q (size p) [::] p.

Lemma ediv_rec_seqE :
 forall n (q qq p : {poly K}),
  ediv_rec_seq (trans_poly CK q) n (trans_poly CK qq) (trans_poly CK p) =
  (trans_poly CK (ediv_rec q n qq p).1,trans_poly CK (ediv_rec q n qq p).2).
Proof.
elim=> [|n ih] q qq r /=; rewrite !size_trans_poly; case: ifP=> //= _.
  by rewrite add_seqE sub_seqE !mul_seqE polyC_seqE indetE cudivE
             !lead_coef_seqE.
by rewrite -ih add_seqE sub_seqE !mul_seqE polyC_seqE cudivE indetE
           !lead_coef_seqE.
Qed.

Lemma ediv_seqE : forall p q : {poly K},
  ediv_seq (trans_poly CK p) (trans_poly CK q) =
  (trans_poly CK (ediv p q).1, trans_poly CK (ediv p q).2).
Proof.
rewrite /ediv /ediv_seq=> p q; rewrite trans_poly_eq0.
case: ifP => /= _.
  by rewrite /trans_poly polyseq0.
by rewrite size_trans_poly -ediv_rec_seqE /trans_poly polyseq0.
Qed.

(* CEuclideanRing structure *)
Lemma temp : forall (p : {poly K}), size (trans_poly CK p) = size p.
Proof. by move=> p; rewrite size_trans_poly. Qed.

Definition seq_ceuclidRingMixin := CEuclidRingMixin temp ediv_seqE.

Canonical Structure seq_ceuclidRingType :=
  Eval hnf in CEuclidRingType [euclidRingType of {poly K}] seq_ceuclidRingMixin.

(* This should be enough to build the other structures! *)

(* DvdRing structure for k[x] *)
Definition codiv_seq (a b : seq CK) := let (q, r) := cediv a b in
  if r == (zero _) then Some (if b == (zero _)
     then (zero (seq_czType CK)) else q) else None.

Lemma codiv_seqE : forall x y,
  omap (trans_poly CK) (x %/? y) = codiv_seq (trans_poly CK x) (trans_poly CK y).
Proof.
move=> x y.
rewrite /codiv_seq -cedivE !trans_poly_eq0 /odivr /= /EuclideanRing.Mixins.odiv.
rewrite /= /divr /modr /edivr /=.
case: ediv=> a b /=.
do 2! case: ifP => _ //=.
by rewrite -zeroE.
Qed.

Definition seqK_cdvdRingMixin := CDvdRingMixin codiv_seqE.

Canonical Structure seqK_cdvdRingType :=
  Eval hnf in CDvdRingType [dvdRingType of {poly K}] seqK_cdvdRingMixin.


(* CGcdRing structure for k[x] *)
Definition gcd_seq a b :=
  let: (a1, b1) := if size a < size b then (b, a) else (a, b) in
  if a1 == [::] then b1 else
  let fix loop (n : nat) (aa bb : seq CK) {struct n} :=
      let rr := (ediv_seq aa bb).2 in
      if rr == [::] then bb else
      if n is n1.+1 then loop n1 bb rr else rr in
  loop (size a1) a1 b1.

Lemma gcd_seqE :
  {morph (trans_poly CK) : p q / gcdr (p : {poly K}) q >-> gcd_seq p q}.
Proof.
rewrite /gcdr /gcd_seq /= /EuclideanRing.Mixins.gcd /= => p q.
rewrite !size_trans_poly.
wlog sqp: p q / size q <= size p=>[hwlog|].
  case: ltnP=> sqp.
    by move/hwlog:(ltnW sqp); rewrite ltnNge (ltnW sqp).
  by move/hwlog:(sqp); rewrite ltnNge sqp.
rewrite ltnNge sqp /= trans_poly_eq0 size_trans_poly.
case: ifP => // _.
remember (size p) as n; rewrite -Heqn; clear Heqn sqp.
by elim: n q p=> [|n ih] p q; rewrite ediv_seqE /= trans_poly_eq0; case: ifP.
Qed.

Definition seqK_cgcdRingMixin := CGcdRingMixin gcd_seqE.

Canonical Structure seqK_cgcdRingType :=
  Eval hnf in CGcdRingType [gcdRingType of {poly K}] seqK_cgcdRingMixin.

(* CBezoutRing structure for k[x] *)

Fixpoint egcd_rec (a b : seq CK) n {struct n} : seq CK * seq CK :=
  if n is n'.+1 then
    if b == [::] then ([:: one CK],[::]) else
    let: (u, v) := egcd_rec b (ediv_seq a b).2 n' in
      (v, (sub_seq u (mul_seq v (ediv_seq a b).1)))
  else ([:: one CK], [::]).

Definition egcd_seq p q := egcd_rec p q (size q).

Lemma egcd_rec_seqE : forall (p q : {poly K}),
  egcd_seq (trans_poly CK p) (trans_poly CK q) =
  (trans_poly CK (bezout p q).1, trans_poly CK (bezout p q).2).
Proof.
move=> p q.
rewrite /egcd_seq /bezout /= /EuclideanRing.Mixins.egcd /=.
rewrite size_trans_poly.
remember (size q) as n; rewrite -Heqn; clear Heqn.
elim: n p q => /= [|n ih p q].
  by rewrite trans_poly1 trans_poly0.
rewrite trans_poly_eq0.
case: ifP => q0.
  by rewrite trans_poly1 trans_poly0.
rewrite ediv_seqE ih -mul_seqE -sub_seqE /EuclideanRing.Mixins.div q0.
by case: EuclideanRing.Mixins.egcd_rec.
Qed.

End KX.
End KX.
