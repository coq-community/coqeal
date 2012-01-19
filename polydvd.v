Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg.
Require Import matrix poly. (*  generic_quotient. *)
Require Import bigop dvdring.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Local fix for poly notations *)
Delimit Scope poly_scope with P.

Notation "m %/ d" := (divp m d) : poly_scope.
Notation "m %% d" := (modp m d) : poly_scope.
Notation "p %| q" := (dvdp p q) : poly_scope.
Notation "p %= q" := (eqp p q) : poly_scope.

Local Open Scope ring_scope.

Module PolyDvdRing.
Section PolyDvdRing.

Variable R : dvdRingType.

Implicit Types p q : {poly R}.

(* Long division of polynomials *)
Definition odivp_rec q :=
  let sq := size q in
  let lq := lead_coef q in
  fix loop (n : nat) (r p : {poly R}) {struct n} :=
    if p == 0 then Some r else
    if size p < sq then None else
    match odivr (lead_coef p) lq with
      | Some x => let m  := x%:P * 'X^(size p - sq) in
                  let r1 := r + m in
                  let p1 := p - m * q in
                  if n is n1.+1 then loop n1 r1 p1 else None
      | None   => None
    end.

Definition odivp p q : option {poly R} :=
  if p == 0 then Some 0 else odivp_rec q (size p) 0 p.

Lemma odivp_recP : forall q n p r, size p <= n ->
  DvdRing.div_spec p q (omap (fun x => x - r) (odivp_rec q n r p)).
Proof.
move=> q; elim=> [|n ihn] p r hn /=.
  case: ifP=> p0 /=; first by constructor; rewrite subrr mul0r (eqP p0).
  by rewrite leqn0 size_poly_eq0 p0 in hn.
case: ifP=> p0 /=; first by constructor; rewrite subrr mul0r (eqP p0).
case: ifP=> spq.
  constructor=> s.
  apply/negP => /eqP hp.
  rewrite hp in spq.
  move/negP: p0 => /negP; rewrite hp mulf_eq0 negb_or; case/andP=> s0 q0.
  move: spq; rewrite (@size_proper_mul _ s q).
    rewrite prednK; last by rewrite addn_gt0 lt0n size_poly_eq0 s0.
    rewrite leqNgt // ltn_neqAle leq_addl.
    by rewrite (eqn_addr _ 0) eq_sym size_poly_eq0 s0.
  by rewrite mulf_neq0 // lead_coef_eq0 (s0, q0).
case: odivrP=> /= [x hx|hpq]; last first.
  by constructor=> s; apply: contra (hpq _) => /eqP ->; rewrite lead_coef_Imul.
set m  := _ * _.
set d  := odivp_rec _ _ _ _.
set om := omap (+%R^~ (- (r + m))) d.
move: (erefl om); rewrite /om /d; case: {2}_ / ihn.
* suff H : size (p - m * q) < size p by rewrite -ltnS (leq_trans H).
  move: hx.
  rewrite -{2}[q]coefK -{2}[p]coefK !lead_coefE !poly_def.
  case hsp: (size p) spq => [|sp] spq.
    by move/eqP: hsp; rewrite size_poly_eq0 p0.
  case hsq: (size q) spq => [|sq] spq.
    move/eqP: hsq; rewrite size_poly_eq0 => /eqP->.
    rewrite coef0 mulr0 => /eqP.
    by rewrite -hsp -lead_coefE lead_coef_eq0 p0.
  move: spq; rewrite ltnS ltnNge => /negPn spq.
  rewrite ![_.-1]/= !big_ord_recr [_ - _]/= -!poly_def=> ->.
  rewrite [m * _]mulrC /m hsp hsq subSS mulr_addl oppr_add.
  rewrite addrAC -!addrA [xx in _ + (_ + xx)]addrC -scaler_mull.
  rewrite [_ ^+ _ * (_ * _)]mulrCA -exprn_addr subnKC //.
  rewrite scaler_mulr -scalerA [_ *: _]scale_polyE subrr addr0.
  rewrite ltnS (leq_trans (size_add _ _)) //.
  rewrite leq_maxl (leq_trans (size_poly _ _)) //.
  rewrite size_opp (leq_trans (size_mul _ _)) //.
  case x0: (x == 0).
    rewrite (eqP x0) polyC0 mul0r size_poly0 addn0.
    rewrite -subn1 leq_sub_add (leq_trans (size_poly _ _)) //.
    by rewrite add1n (leq_trans spq) // leqnSn.
  rewrite size_proper_mul ?lead_coefC ?lead_coefXn ?mulr1 ?x0 //.
  rewrite size_polyC x0 size_polyXn /= addnS /=.
  by rewrite addn_subA // leq_sub_add leq_add2r size_poly.
* move=> s hs; case hpq: (odivp_rec _ _ _ _)=> [r'|] //=.
  case=> hm; constructor; move: hm; rewrite oppr_add addrA.
  move/eqP; rewrite (can2_eq (@addrNK _ _) (@addrK _ _)); move/eqP->.
  by rewrite mulr_addl -hs addrNK.
* move=> hpq; case hpq': (odivp_rec _ _ _ _)=> [r'|] //= _.
  constructor=> s; apply: contra (hpq (s - m)); move/eqP->.
  by rewrite mulr_subl.
Qed.

Lemma odivpP : forall p q, DvdRing.div_spec p q (odivp p q).
Proof.
move=> p q; rewrite /odivp.
case p0: (p == 0); first by constructor; rewrite mul0r (eqP p0).
have := (@odivp_recP q (size p) p 0 (leqnn _)).
by case: odivp_rec=> [a|] //=; rewrite subr0; apply.
Qed.

Definition polyDvdRingMixin := DvdRingMixin odivpP.

Canonical Structure polyDvdRingType := DvdRingType {poly R} polyDvdRingMixin.

End PolyDvdRing.
End PolyDvdRing.

Module PolyGcdRing.
Section PolyGcdRing.

(* Polyonomials over gcd rings *)

Import PolyDvdRing.

Variable R : gcdRingType.
Implicit Types a b : R.

Implicit Types p q : {poly R}.

(* Useful lemmas *)

(* Double induction for polynomials *)
Lemma poly_ind2 : forall P : {poly R} -> {poly R} -> Type,
  (forall p, P p 0) ->
  (forall q, P 0 q) ->
  (forall c p d q, P p (q * 'X + d%:P) ->
                   P (p * 'X + c%:P) q ->
                   P (p * 'X + c%:P) (q * 'X + d%:P)) ->
  (forall p q, P p q).
Proof.
move=> P H01 H02 H.
apply: (@poly_ind _)=> // p c IH1.
apply: (@poly_ind _)=> // q d IH2.
apply: (@H c p d q)=> //.
Qed.

Lemma elim_poly : forall p, exists p', exists c, p = p' * 'X + c%:P.
Proof.
elim/poly_ind; first by exists 0; exists 0; rewrite mul0r add0r.
by move=> p c [_ [_]] _; exists p; exists c.
Qed.

Lemma polyC_inj_dvdr : forall a b, a %| b -> a%:P %| b %:P.
Proof.
move=> a b.
case/dvdrP=> x Hx; apply/dvdrP; exists (x%:P).
by rewrite -polyC_mul Hx.
Qed.

Lemma polyC_inj_eqd : forall a b, a %= b -> a%:P %= b%:P.
Proof.
by move=> a b; rewrite /eqd; case/andP; do 2 move/polyC_inj_dvdr=> ->.
Qed.


(* Properties of gcdsr *)

Lemma gcdsr0 : gcdsr (0 : {poly R}) = 0.
Proof. by rewrite seq_poly0. Qed.

Lemma gcdsr1 : gcdsr (1 : {poly R}) %= 1.
Proof. by rewrite polyseqC nonzero1r /= gcdr0. Qed.

Lemma gcdsrC : forall c : R, gcdsr c%:P %= c.
Proof.
by move=> c; rewrite polyseqC; case c0: (c == 0); rewrite ?gcdr0 // (eqP c0).
Qed.

Lemma gcdsr_gcdl : forall p c, gcdsr (p * 'X + c%:P) = gcdr c (gcdsr p).
Proof.
move=> p c.
case p0: (p == 0).
  rewrite (eqP p0) mul0r add0r gcdsr0 /gcdsr polyseqC.
  by case c0: (c == 0)=> //=; apply/eqP; rewrite eq_sym (eqP c0) gcdr_eq0 eqxx.
by rewrite -poly_cons_def polyseq_cons size_poly_eq0; case: p0=> ->.
Qed.

Lemma gcdsr_eq0 : forall p, (gcdsr p == 0) = (p == 0).
Proof.
elim/poly_ind=> [|p c IH]; first by rewrite gcdsr0 !eq_refl.
rewrite gcdsr_gcdl gcdr_eq0 IH -[p * 'X + c%:P == 0]size_poly_eq0 size_amulX.
rewrite size_poly_eq0 andbC.
by apply/idP/idP => [->|] //; case: ifP.
Qed.

Lemma gcdsr_mulX : forall p, gcdsr (p * 'X) %= gcdsr p.
Proof. by move=> p; rewrite -[p*'X]addr0 gcdsr_gcdl gcd0r. Qed.

Lemma gcdsrX : gcdsr ('X : {poly R}) %= 1.
Proof.
move: (gcdsr_mulX 1); rewrite mul1r=> H.
exact: (eqd_trans H gcdsr1).
Qed.

Lemma gcdsr_mull : forall a p, gcdsr (a%:P * p) %= a * gcdsr p.
Proof.
move=> a.
elim/poly_ind=> [|p c IH]; first by rewrite mulr0 gcdsr0 mulr0.
rewrite mulr_addr -polyC_mul mulrA gcdsr_gcdl.
rewrite (eqd_trans (eqd_gcd (eqdd _) IH)) //.
by rewrite (eqd_trans (gcdr_mul2l _ _ _)) // -gcdsr_gcdl.
Qed.

Lemma gcdsr_mulr : forall a p, gcdsr (p * a%:P) %= gcdsr p * a.
Proof. by move=> a p; rewrite mulrC [_ * a]mulrC gcdsr_mull. Qed.

Lemma mulr_gcdsr : forall a p, a * gcdsr p %= gcdsr (a%:P * p).
Proof. by move=> a p; rewrite eqd_sym gcdsr_mull. Qed.

Lemma mulr_gcdsl : forall a p, gcdsr p * a %= gcdsr (p * a %:P).
Proof. by move=> a p; rewrite eqd_sym gcdsr_mulr. Qed.

Lemma eq_eqdgcdsr : forall p q, p = q -> gcdsr p %= gcdsr q.
Proof. by move=> p q ->. Qed.

(* Key lemma in gauss lemma *)
Lemma gcdr_gcdsr_muladdr : forall a p q, gcdr a (gcdsr (a%:P * p + q)) %= gcdr a (gcdsr q).
Proof.
move=> a.
elim/poly_ind=> [|p c IH q]; first by move=> q; rewrite mulr0 add0r eqdd.
rewrite mulr_addr mulrA -polyC_mul addrC addrA -[q]polyseqK.
elim: q=> /= q _; case: q=> /= [|d p1].
  rewrite add0r gcdsr_gcdl (eqd_trans (gcdrA a _ _)) // -[a*c]addr0.
  rewrite (eqd_trans (eqd_gcd (gcdr_addl_mul a 0 c) (eqdd _))) //.
  by rewrite (eqd_trans (eqd_gcd (gcdr0 a) (eqdd _))) // -[_ * p]addr0 (IH 0).
rewrite poly_cons_def -!addrA [d%:P + _]addrCA -polyC_add addrA -mulr_addl.
rewrite !gcdsr_gcdl [Poly p1 + _]addrC [d+_]addrC (eqd_trans (gcdrA _ _ _)) //.
rewrite (eqd_trans ((eqd_gcd (gcdr_addl_mul a d c)) (eqdd _))) //.
rewrite (eqd_trans (gcdrAC _ _ _)) ?(eqd_trans (eqd_gcd (IH _) (eqdd d))) //.
rewrite (eqd_trans (gcdrAC _ _ _)) // eqd_sym (eqd_trans (gcdrA _ _ _)) //.
Qed.


(* Primitive polynomials *)

(* = is too strict, consider: cont (-3%P) %= 3... *)
Definition primitive p := gcdsr p %= 1.

Lemma primitive0 : forall p, primitive p -> p != 0.
Proof.
rewrite /primitive=> p pp; apply/negP=> p0; move: pp.
rewrite (eqP p0) gcdsr0 eqd_def dvd0r; case/andP=> H _.
by move: (nonzero1r R); rewrite H.
Qed.

(* Another key lemma *)
Lemma gcdsr_primitive : forall p, exists q, p = (gcdsr p)%:P * q /\ primitive q.
Proof.
move=> p; rewrite /primitive.
suff H: exists q, p = (gcdsr p)%:P * q.
  case p0: (p == 0); first by exists 1; rewrite (eqP p0) gcdsr0 mulr1 gcdsr1.
  case: H=> x H; exists x; split=> //.
  rewrite -(@eqd_mul2l _ (gcdsr p)).
    by rewrite mulr1 {2}H (eqd_trans _ (mulr_gcdsr _ x)).
  by apply/negP; move/eqP=> c0; move: H; rewrite c0 mul0r; move/eqP: p0.
elim/poly_ind: p=> /= [|p c [q IH]]; first by exists 1; rewrite gcdsr0 mul0r.
case/dvdrP: (dvdr_gcdr c (gcdsr p))=> wr Hr; rewrite mulrC in Hr.
case/dvdrP: (dvdr_gcdl c (gcdsr p))=> wl Hl; rewrite mulrC in Hl.
exists (wr%:P * q * 'X + wl%:P).
by rewrite mulr_addr gcdsr_gcdl !mulrA -!polyC_mul -Hl -Hr -IH.
Qed.

Lemma gcdsr_dvdr : forall p, (gcdsr p)%:P %| p.
Proof.
move=> p; case: (gcdsr_primitive p)=> x [? _]; apply/dvdrP.
by exists x; rewrite mulrC.
Qed.

Lemma gcdsr_odivp :
  forall p, p != 0 -> exists x, p %/? (gcdsr p)%:P = Some (x : {poly R}) /\ primitive x.
Proof.
move=> p p0; case: (gcdsr_primitive p)=> x [Hp primx].
exists x; split=> //.
rewrite {1}Hp odivr_mulKr //.
by apply/negP=> H; move: Hp p0; rewrite (eqP H) mul0r=> ->; rewrite eq_refl.
Qed.

Lemma prim_mulX : forall p, primitive p -> primitive (p * 'X).
Proof.
rewrite /primitive=> p H; apply: (@eqd_trans _ (gcdsr p) _ 1)=> //.
by rewrite -[p * _]addr0 gcdsr_gcdl (eqd_trans (gcd0r _)).
Qed.

Lemma gauss_lemma : forall p q, gcdsr (p * q) %= gcdsr p * gcdsr q.
Proof.
apply: @poly_ind2=> [p|q|p0 p1 q0 q1]; first by rewrite mulr0 !gcdsr0 mulr0.
  by rewrite mul0r !gcdsr0 mul0r.
set p := p1 * 'X + p0%:P.
set q := q1 * 'X + q0%:P.
move=> IH1 IH2.
case: (gcdsr_primitive p); rewrite /primitive=> p' [Hp prim_p'].
case: (gcdsr_primitive q); rewrite /primitive=> q' [Hq prim_q'].
case: (elim_poly p')=> p1' [p0'] Hp'.
case: (elim_poly q')=> q1' [q0'] Hq'.

(* First some preliminary results *)
case H0p0 : (p0 == 0).
  rewrite /p (eqP H0p0) addr0 -mulrA ['X * _]mulrC mulrA.
  rewrite (eqd_trans (gcdsr_mulX _)) // (eqd_trans IH1) //.
  by  rewrite eqd_sym (eqd_mul (gcdsr_mulX _)).
case H0q0 : (q0 == 0).
  rewrite /q (eqP H0q0) addr0 mulrA (eqd_trans (gcdsr_mulX _)) //.
  by rewrite (eqd_trans IH2) // eqd_sym (eqd_mul _ (gcdsr_mulX _)).
have Hp1p1' : p1 = (gcdsr p)%:P * p1'.
  apply/polyP=> i; move: Hp; rewrite {1}/p Hp' mulr_addr mulrA -polyC_mul.
  move/polyP=> H; move: (H (i.+1)); rewrite -!poly_cons_def !coef_cons.
  by case i.
have Hq1q1' : q1 = (gcdsr q)%:P * q1'.
  apply/polyP=> i; move: Hq; rewrite {1}/q Hq' mulr_addr mulrA -polyC_mul.
  move/polyP=> H; move: (H (i.+1)); rewrite -!poly_cons_def !coef_cons.
  by case i.
have Hgcdsrp0 : (gcdsr p != 0) by rewrite /p gcdsr_gcdl gcdr_eq0 H0p0.
have Hgcdsrq0 : (gcdsr q != 0) by rewrite /q gcdsr_gcdl gcdr_eq0 H0q0.

(* Massage induction hypotheses *)
have IH1' : gcdsr (p1' * q') %= gcdsr p1'.
  rewrite -(@eqd_mul2r _ (gcdsr q)) ?(eqd_trans (mulr_gcdsl _ _)) // -mulrA.
  rewrite [q' * _]mulrC -Hq -(@eqd_mul2l _ (gcdsr p)) // mulrA.
  rewrite (eqd_trans (mulr_gcdsr _ _)) // mulrA -Hp1p1' eqd_sym.
  by rewrite (eqd_trans (eqd_mul (mulr_gcdsr _ _) (eqdd _))) // -Hp1p1' eqd_sym.
have IH2' : gcdsr (p' * q1') %= gcdsr q1'.
  rewrite -(@eqd_mul2l _ (gcdsr p)) ?(eqd_trans (mulr_gcdsr _ _)) // mulrA.
  rewrite -Hp -(@eqd_mul2r _ (gcdsr q)) // (eqd_trans (mulr_gcdsl _ _)) //.
  rewrite -!mulrA [q1' * _]mulrC -Hq1q1' eqd_sym mulrC [gcdsr q1' * _]mulrC.
  by rewrite (eqd_trans (eqd_mul (mulr_gcdsr _ _) (eqdd _))) // -Hq1q1' mulrC eqd_sym.

(* Simplify goal *)
suff Hprim : (gcdsr (p' * q') %= 1).
  rewrite {1}Hp {1}Hq mulrAC mulrA -polyC_mul-mulrA.
  rewrite (eqd_trans (gcdsr_mull _ _)) // [q' * _]mulrC -{2}[gcdsr q]mulr1.
  rewrite mulrA (eqd_mul _ _) //.

(* Simplify further *)
rewrite Hp' Hq' mulrC.
rewrite mulr_addr !mulr_addl -polyC_mul mulrCA [_ * p0'%:P]mulrC !mulrA.
rewrite !addrA -mulr_addl -mulr_addl.

(* Finish everything *)
rewrite gcdsr_gcdl -/(coprimer _ _) coprimer_mull andbC /coprimer {1}addrC.
rewrite [_ + q0'%:P * p1']addrC -addrA (eqd_trans (gcdr_gcdsr_muladdr _ _ _)).
  rewrite (eqd_trans (gcdr_gcdsr_muladdr _ _ _)) // -mulrA [_ * 'X]mulrC mulrA.
  rewrite -mulr_addl -Hp' (eqd_trans (eqd_gcd (eqdd _) IH2')) // -gcdsr_gcdl.
  by rewrite -Hq'.
rewrite [_ * p1']mulrC -mulrA -mulr_addr addrC -Hq'.
by rewrite (eqd_trans (eqd_gcd (eqdd _) IH1')) // -gcdsr_gcdl -Hp'.
Qed.

Lemma gauss_primitive : forall p q, primitive p -> primitive q -> primitive (p * q).
Proof.
rewrite /primitive=> p q pp pq.
by rewrite (eqd_trans (gauss_lemma _ _)) // (eqd_trans (eqd_mul pp pq)) // mul1r.
Qed.

Lemma gcdsr_inj_dvdr : forall p q, p %| q -> gcdsr p %| gcdsr q.
Proof.
move=> p q; case/dvdrP=> x ->.
move: (gauss_lemma x p).
case/andP=> _ H.
by rewrite (dvdr_trans _ H) ?dvdr_mull //.
Qed.

Lemma gcdsr_inj_eqd : forall p q, p %= q -> gcdsr p %= gcdsr q.
Proof.
move=> p q; case/andP=> pq qp; apply/andP.
by rewrite (gcdsr_inj_dvdr pq) (gcdsr_inj_dvdr qp).
Qed.


(* Primitive part, pp *)

Definition pp p := match p %/? (gcdsr p)%:P with
  | Some x => x
  | None   => 1
  end.

Lemma pp0 : pp 0 = 0.
Proof. by rewrite /pp /odivr gcdsr0 /= /odivp eq_refl. Qed.

Lemma ppP : forall p, p = (gcdsr p)%:P * pp p.
Proof.
move=> p.
case p0: (p == 0); first by rewrite (eqP p0) pp0 mulr0.
have g0 : (gcdsr p)%:P != 0 by apply/eqP; move/eqP; rewrite polyC_eq0 gcdsr_eq0 p0.
case: (gcdsr_odivp (negbT p0))=> x [hx px].
by rewrite /pp hx; move: (odivr_some hx)=> {1}->.
Qed.

Lemma pp_eq0 : forall p, (pp p == 0) = (p == 0).
Proof.
move=> p.
rewrite {2}(ppP p) mulf_eq0.
apply/idP/idP; first by move->; rewrite orbT.
case/orP=> //.
by rewrite polyC_eq0 gcdsr_eq0; move/eqP->; rewrite pp0.
Qed.

Lemma ppC : forall c, c != 0 -> pp c%:P %= 1.
Proof.
move=> c c0.
move: (eqd_trans (polyC_inj_eqd (gcdsrC c)) (eq_eqd (ppP c%:P))).
rewrite -{1}[(gcdsr c%:P)%:P]mulr1.
have g0: ((gcdsr c%:P)%:P != 0).
  by apply/negP; rewrite polyC_eq0 gcdsr_eq0 polyC_eq0=> H; rewrite H in c0.
by rewrite (eqd_mul2l _ _ g0) eqd_sym.
Qed.

Lemma pp1 : pp 1 %= 1.
Proof. by rewrite ppC ?nonzero1r. Qed.

Lemma ppX : pp 'X %= 'X.
Proof.
by rewrite {2}(ppP 'X) -{1}[pp _]mul1r eqd_mul // eqd_sym (polyC_inj_eqd gcdsrX).
Qed.

Lemma prim_pp : forall p, p != 0 -> primitive (pp p).
Proof. by move=> p p0; rewrite /pp; case: (gcdsr_odivp p0)=> x [-> px]. Qed.

Lemma pp_prim : forall p, primitive p -> (p %= pp p).
Proof.
rewrite /primitive=> p pp.
by rewrite {1}(ppP p) -{2}[PolyGcdRing.pp p]mul1r eqd_mul // polyC_inj_eqd.
Qed.

Lemma pp_dvdr : forall p, pp p %| p.
Proof. by move=> p; apply/dvdrP; exists (gcdsr p)%:P; exact: ppP. Qed.

Lemma pp_mul : forall p q, pp (p * q) %= pp p * pp q.
Proof.
move=> p q.
case p0: (p == 0); first by rewrite (eqP p0) mul0r !pp0 mul0r.
case q0: (q == 0); first by rewrite (eqP q0) mulr0 !pp0 mulr0.
have h0: (gcdsr (p * q))%:P != 0.
  by rewrite polyC_eq0 gcdsr_eq0 mulf_eq0 p0 q0.
have h1: pp p * pp q != 0.
  by apply/negP; rewrite mulf_eq0 !pp_eq0 p0 q0.
rewrite -(eqd_mul2l _ _ h0) -ppP.
move: (polyC_inj_eqd (gauss_lemma p q)).
rewrite -(eqd_mul2r _ _ h1)=> H; rewrite eqd_sym (eqd_trans H); first by done.
by rewrite polyC_mul mulrCA -mulrA -ppP mulrCA mulrA -ppP.
Qed.

Lemma pp_mull : forall a p, a != 0 -> pp (a%:P * p) %= pp p.
Proof.
move=> a p a0.
rewrite (eqd_trans (pp_mul a%:P p)) //.
by rewrite -{2}[pp p]mul1r eqd_mul ?ppC ?(eqP a0).
Qed.

Lemma pp_mulX : forall p, pp (p * 'X) %= pp p * 'X.
Proof. by move=> p; rewrite (eqd_trans (pp_mul _ _)) // eqd_mul // ppX. Qed.

Lemma pp_inj_dvdr : forall p q, p %| q -> pp p %| pp q.
Proof.
move=> p q; case/dvdrP=> x ->.
move: (pp_mul x p).
by case/andP=> _ H; rewrite (dvdr_trans _ H) ?dvdr_mull //.
Qed.

Lemma pp_inj_eqd : forall p q, p %= q -> pp p %= pp q.
Proof.
move=> p q.
by case/andP=> pq qp; apply/andP; rewrite (pp_inj_dvdr pq) (pp_inj_dvdr qp).
Qed.

Lemma size_pp : forall p, size p = size (pp p).
Proof.
move=> p.
case p0: (p == 0); first  by rewrite (eqP p0) pp0.
have gp0: (gcdsr p != 0) by rewrite gcdsr_eq0 (negbT p0).
apply/eqP; rewrite eqn_leq.
apply/andP; split.
  move: (size_mul (gcdsr p)%:P (pp p)).
  by rewrite {5}(ppP p) size_polyC gp0.
rewrite {2}(ppP p).
elim/poly_ind: (pp p)=> [|q c IH]; first by rewrite size_poly0 leq0n.
rewrite mulr_addr mulrA -polyC_mul !size_amulX.
case: ifP=>[|H]; first by rewrite leq0n.
case: ifP=>//.
case/andP=> H1 H2.
rewrite mulf_eq0 in H2.
case/orP: H2 => G; first by rewrite G in gp0.
case/nandP: H=> H; last by move: H; rewrite G.
rewrite size_poly_eq0 mulf_eq0 in H1.
case/orP: H1; rewrite ?polyC_eq0=> H2; first by move: gp0; rewrite H2.
by rewrite (eqP H2) size_poly_eq0 eq_refl in H.
Qed.

Lemma dvdrp_spec : forall p q, (p %| q) = (gcdsr p %| gcdsr q) && (pp p %| pp q).
Proof.
move=> p q.
apply/idP/idP=> [H|]; first by rewrite gcdsr_inj_dvdr ?pp_inj_dvdr.
by case/andP=> ? ?; rewrite (ppP p) (ppP q) dvdr_mul // polyC_inj_dvdr.
Qed.

Lemma pp_prim_eq : forall p, p != 0 -> primitive p = (p %= pp p).
Proof.
move=> p p0.
apply/idP/idP; first exact: pp_prim.
case/andP=> H _.
move: (prim_pp p0).
rewrite /primitive eqd_def; case/andP=> gp1 _.
move: H; rewrite dvdrp_spec; case/andP=> gp2 _.
by apply/andP; rewrite (dvdr_trans gp2 gp1) dvd1r.
Qed.

Lemma dvdrp_prim_mull : forall a p q,
  a != 0 ->  primitive q -> p %| a%:P * q = (gcdsr p %| a) && (pp p %| q).
Proof.
move=> a p q a0 pq; case/andP: (pq)=> pq1 pq2.
rewrite dvdrp_spec.
case/andP: (gcdsr_mull a q)=> Hg2 Hg3.
case/andP: (pp_mul (a%:P) q)=> pp1 pp2.
apply/idP/idP; case/andP=> H Hpp.
  move: (dvdr_mul pq1 (dvdrr a)); rewrite mulrC.
  move/(dvdr_trans (dvdr_trans H Hg2)); rewrite mul1r=>-> /=.
  rewrite (dvdr_trans _ (pp_dvdr q)) //.
  move: (dvdr_trans Hpp pp1)=> H'.
  case/andP: (ppC a0)=> H1 _.
  by move: (dvdr_trans H' (dvdr_mul H1 (dvdrr (pp q)))); rewrite mul1r.
rewrite (dvdr_trans _ Hg3) /=; last by move: (dvdr_mul H pq2); rewrite mulr1.
case/andP: (pp_prim pq)=> G1 _.
by rewrite (dvdr_trans (dvdr_trans Hpp G1)); case/andP: (pp_mull q a0).
Qed.

Lemma dvdrpC : forall a p, a%:P %| p = (a %| gcdsr p).
Proof.
move=> a p.
apply/idP/idP=> [|H]; last exact: (dvdr_trans (polyC_inj_dvdr H) (gcdsr_dvdr p)).
rewrite dvdrp_spec; case/andP=> H _; case/andP: (gcdsrC a)=> _ G.
exact: (dvdr_trans G H).
Qed.

Lemma dvdrp_primr : forall p q, p %| q -> primitive q -> primitive p.
Proof.
move=> p q.
case p0: (p == 0); first by rewrite (eqP p0) dvd0r; move/eqP->.
rewrite /primitive /eqd=> pq ppq; rewrite dvd1r andbT; apply/dvdrP.
move: (pp_inj_dvdr pq)=> pppq; rewrite dvdrp_spec in pq.
case/andP: pq; case/dvdrP=> x Hx; case/dvdrP=> y Hy.
case/andP: ppq; case/dvdrP=> z Hz _.
by exists (z * x); rewrite -mulrA -Hx -Hz.
Qed.

Lemma dvdrp_priml : forall a p q, a != 0 -> p %| a%:P * q -> primitive p -> p %| q.
Proof.
move=> a p q a0.
rewrite dvdrp_spec; case/andP=> H1 H2.
rewrite /primitive /eqd dvdrp_spec; case/andP=> H3 _.
case/andP: (pp_mull q a0)=> H4 _.
by rewrite (dvdr_trans H2 H4) (dvdr_trans H3 (dvd1r (gcdsr q))).
Qed.

(* gcdp *)
Fixpoint gcdp_rec (n : nat) (p q : {poly R}) :=
  let r := modp p q in
  if r == 0 then q
            else if n is n'.+1 then gcdp_rec n' q (pp r) else pp r.

Definition gcdp p q :=
  let (p1,q1) := if size p < size q then (q,p) else (p,q) in
  let d  := (gcdr (gcdsr p1) (gcdsr q1))%:P in
  d * gcdp_rec (size (pp p1)) (pp p1) (pp q1).

Lemma gcdp_rec0r : forall p n, gcdp_rec n 0 p = p.
Proof. by move=> p n; rewrite /gcdp_rec; case: n; rewrite mod0p eq_refl. Qed.

Lemma gcdp_recr0 : forall p n, primitive p -> gcdp_rec n p 0 %= p.
Proof.
move=> p n pp.
have p0 : (p == 0) = false by apply/negP; move/negP: (primitive0 pp).
have Hppp : PolyGcdRing.pp p %= p
  by rewrite {2}(ppP p) -{1}[PolyGcdRing.pp p]mul1r eqd_mul // eqd_sym polyC_inj_eqd.
by case: n=> /= [|n]; rewrite modp0 p0 ?gcdp_rec0r Hppp.
Qed.

(* Show that gcdp_rec return a primitive polynomial that is the gcd of p and q *)
Lemma gcdp_recP : forall n p q g,
   size q <= n -> q != 0 -> primitive q ->
  (g %| gcdp_rec n p q = (g %| p) && (g %| q)) /\ primitive (gcdp_rec n p q).
Proof.
elim=> /= [p q g|n IH p q g sqn q0 pq].
  by rewrite leqn0 size_poly_eq0=> ->.

(* Recall the specifiction of pseudo-division *)
move: (divCp_spec p q).
set lx := lead_coef q ^+ scalp p q.
rewrite -mul_polyC=> Hdiv.
have H0: lx != 0.
  apply/negP; rewrite expf_eq0 lead_coef_eq0; case/andP=> _ H0.
  by move: q0; rewrite H0.

case: ifP=>[pq0|npq0].
  split=> //; apply/idP/idP; last by case/andP.
  move=> gq; rewrite gq andbT.
  rewrite (eqP pq0) addr0 in Hdiv.
  move: (dvdr_mull (p %/ q)%P gq); rewrite -Hdiv=> H.
  by rewrite (dvdrp_priml H0 H) // (dvdrp_primr gq).

set pp_pq := pp (p %% q)%P.
have s_pp_pq : (size pp_pq <= n)
  by rewrite -size_pp; move: (leq_trans (modp_spec p q0) sqn); rewrite ltnS.
have p_pp_pq : primitive pp_pq by rewrite prim_pp // npq0.
have pp_pq0 : pp_pq != 0 by rewrite pp_eq0 npq0.

(* Apply induction hypothesis *)
case: (IH q pp_pq g s_pp_pq pp_pq0 p_pp_pq)=> -> h2 /=; split=>//.

apply/idP/idP.

  (* Case: (g %| q) && (g %| pp_pq) -> (g %| p) && (g %| q) *)
  case/andP=> gq gpppq; rewrite gq andbT.
  move: (dvdr_mull (gcdsr (p %% q)%P)%:P gpppq); rewrite -(ppP _)=> gpmq.
  move: (dvdr_add (dvdr_mull (p %/ q)%P gq) gpmq); rewrite -Hdiv=> H.
  by rewrite (dvdrp_priml H0 H) // (dvdrp_primr gq).

(* Case: (g %| p) && (g %| q) -> (g %| q) && (g %| pp_pq) *)
(* Simplify the goal *)
case/andP=> gp gq; rewrite gq /=.

move: (dvdr_sub (dvdr_mull lx%:P gp) (dvdr_mull (p %/ q)%P gq)).
move/eqP: Hdiv; rewrite addrC -subr_eq => /eqP->; rewrite dvdrp_spec=> gpq.

suff gppg : g %| pp g by rewrite (dvdr_trans gppg) //; case/andP: gpq.
move: (dvdrp_primr gq pq).
by rewrite (pp_prim_eq (primitive0 (dvdrp_primr gq pq))); case/andP.
Qed.

(* Correctness of gcdp *)
Lemma gcdpP : forall p q g, g %| gcdp p q = (g %| p) && (g %| q).
Proof.
rewrite /gcdp=> p q g.

(* Simplify the goal *)
wlog sqp : p q / size q <= size p=> [H|].
  case: ltnP=> spq.
     by move/H: (ltnW spq); rewrite ltnNge (ltnW spq) andbC.
    by move/H: (spq); rewrite ltnNge spq.
rewrite ltnNge sqp /=.

(* Cases when either input is zero *)
case p0: (p == 0).
  have q0: (q == 0) by rewrite (eqP p0) size_poly0 leqn0 size_poly_eq0 in sqp.
  by rewrite (eqP p0) (eqP q0) !pp0 size_poly0 gcdp_rec0r mulr0 andbb.
case q0: (q == 0).
  rewrite (eqP q0) dvdr0 andbT gcdsr0 pp0 /=.
  case/andP: (gcdp_recr0 (size (pp p)) (prim_pp (negbT p0)))=> Hg Hpp.
  apply/idP/idP=> [H|].
    rewrite (ppP p); case/andP: (gcdr0 (gcdsr p))=> H0 _.
    exact: (dvdr_trans H (dvdr_mul (polyC_inj_dvdr H0) Hg)).
  rewrite dvdrp_spec {3}(ppP g); case/andP=> Hgp Hppgp.
  case/andP: (gcdr0 (gcdsr p))=> _ H0.
  exact: (dvdr_mul (polyC_inj_dvdr (dvdr_trans Hgp H0)) (dvdr_trans Hppgp Hpp)).

have ppq0 : pp q != 0 by rewrite pp_eq0 (negbT q0).
have spp: (size (pp q) <= size (pp p)) by rewrite -!size_pp.

case: (gcdp_recP (pp p) (pp g) spp ppq0 (prim_pp (negbT q0)))=> H prim.

apply/idP/idP; last first.
  (* The easier case:
       g | p /\ g | q -> q | gcd (cont p) (cont q) * gcdp_rec (pp p) (pp q)
  *)
  rewrite {3}(ppP g); case/andP=> gp gq.
  apply/dvdr_mul; last by rewrite H (pp_inj_dvdr gp) (pp_inj_dvdr gq).
  by rewrite polyC_inj_dvdr // dvdr_gcd (gcdsr_inj_dvdr gp) (gcdsr_inj_dvdr gq).

(* The harder case:
     q | gcd (cont p) (cont q) * gcdp_rec (pp p) (pp q) -> g | p /\ g | q
*)
have g0 : (gcdr (gcdsr p) (gcdsr q)) != 0
  by apply/negP; rewrite gcdr_eq0 !gcdsr_eq0 p0 q0.

rewrite (dvdrp_prim_mull _ g0 prim); case/andP=> gdvd ppgdvd.

have Hgg: gcdsr g %| gcdsr p /\ gcdsr g %| gcdsr q.
  by rewrite -dvdrpC (dvdr_trans _ (gcdsr_dvdr _)) ?polyC_inj_dvdr
             ?(dvdr_trans gdvd (dvdr_gcdl _ _))
             ?(dvdr_trans gdvd (dvdr_gcdr _ _)).
have Hppg : (pp g %| pp p) /\ (pp g %| pp q)
  by move: ppgdvd; rewrite H; case/andP.
case: Hgg; case: Hppg=> ? ? ? ?.
by rewrite (ppP g) (ppP p) (ppP q) !dvdr_mul // polyC_inj_dvdr.
Qed.

Definition polyGcdRingMixin := GcdRingMixin gcdpP.
Canonical Structure polyGcdRingType := GcdRingType {poly R} polyGcdRingMixin.

End PolyGcdRing.
End PolyGcdRing.

Module PolyPriField.
Section PolyPriField.

(* This section shows that the polynomial ring k[x] where k is a field is an
   Euclidean ring *)

Variable F : fieldType.
Implicit Types p q r : {poly F}.

Definition ediv_rec q :=
  let sq := size q in
  let lq := lead_coef q in
  fix loop (n : nat) (qq r : {poly F}) {struct n} :=
    if size r < sq then (qq, r) else
    let m := (lead_coef r / lq)%:P * 'X^(size r - sq) in
    let qq1 := qq + m in
    let r1 := r - m * q in
    if n is n1.+1 then loop n1 qq1 r1 else (qq1, r1).

Definition ediv p q : {poly F} * {poly F} :=
  if q == 0 then (0, p) else ediv_rec q (size p) 0 p.

Lemma ediv_recP : forall q n p qq, q != 0 -> size p <= n ->
    let: (qq', r) := (ediv_rec q n qq p) in
  EuclideanRing.edivr_spec (size : {poly F} -> nat) p q (qq' - qq, r).
Proof.
move=> q.
elim=> [|n IHn] p qq Hq0 /=.
  rewrite leqn0 size_poly_eq0=> p0; rewrite (eqP p0) /=.
  case: ifP; first by constructor; [rewrite subrr mul0r add0r | apply/implyP].
  rewrite size_poly0 lt0n size_poly_eq0=> q0.
  constructor; by rewrite ?q0 // sub0r [qq + _]addrC -addrA subrr addr0 subrr.
case: ifP; first by constructor; [rewrite subrr mul0r add0r | apply/implyP].
move=> spq spSn.
set x :=  (lead_coef p / lead_coef q)%:P * 'X^(size p - size q).
have := IHn (p - x * q) (qq + x).
case hdiv: ediv_rec=> [qq' r].
set q0 := qq' - _; move=> h.
move: (erefl (q0, r)).
case: {1}_ / h=> //.
  suff H :  size (p - x * q) < size p by rewrite -ltnS (leq_trans H).
  rewrite -[q]coefK -{1}[p]coefK !poly_def.
  case hsp: (size p) spq => [|sp] spq.
    by move: spq; rewrite ltnNge leqn0 size_poly_eq0 Hq0.
  case hsq: (size q) spq => [|sq] spq.
    by move: Hq0; move/eqP: hsq; rewrite size_poly_eq0=>->.
  move: spq; rewrite ltnS ltnNge; move/negPn=> spq.
  rewrite !big_ord_recr [_ - _]/= -!poly_def.
  rewrite [x * _]mulrC /x hsp hsq subSS mulr_addl oppr_add.
  rewrite addrAC -!addrA [xx in _ + (_ + xx)]addrC -scaler_mull.
  rewrite [_ ^+ _ * (_ * _)]mulrCA -exprn_addr subnKC //.
  rewrite /lead_coef hsp hsq ![_.+1.-1]/= scaler_mulr ![_ *: _]scale_polyE.
  rewrite !mulrA -polyC_mul -!mulrA [_ * q`_sq]mulrC divff; last first.
    by apply: contra Hq0; rewrite -lead_coef_eq0 /lead_coef hsq.
  rewrite mulr1 subrr addr0.
  rewrite ltnS (leq_trans (size_add _ _)) //.
  rewrite leq_maxl (leq_trans (size_poly _ _)) //.
  rewrite size_opp (leq_trans (size_mul _ _)) //.
  case x0: ((p`_sp / q`_sq) == 0).
    rewrite (eqP x0) polyC0 mul0r size_poly0 addn0.
    rewrite -subn1 leq_sub_add (leq_trans (size_poly _ _)) //.
    by rewrite add1n (leq_trans spq) // leqnSn.
  rewrite size_proper_mul ?lead_coefC ?lead_coefXn ?mulr1 ?x0 //.
  rewrite size_polyC x0 size_polyXn /= addnS /=.
  by rewrite addn_subA // leq_sub_add leq_add2r size_poly.
move=> q1 r0 H G.
move/eqP; rewrite xpair_eqE; case/andP; move/eqP=> q1q0; move/eqP=> r0r.
constructor; last by rewrite -r0r.
move/eqP: H; rewrite subr_eq; move/eqP=> ->.
rewrite q1q0 /q0 r0r !mulr_addl -!addrA [_ + (r + _)]addrCA oppr_add mulr_addl.
by rewrite -addrA [_ * q + _ * q]addrC !mulNr subrr addr0 [_ + r]addrC.
Qed.

Lemma edivP : forall p q,
  EuclideanRing.edivr_spec (size : {poly F} -> nat) p q (ediv p q).
Proof.
move=> p q; rewrite /ediv.
case q0: (q == 0).
 constructor; first by rewrite mul0r add0r.
  by rewrite (eqP q0); apply/implyP; move/eqP.
have := (@ediv_recP q (size p) p 0 (negbT q0) (leqnn _)).
by case: ediv_rec=> a b; rewrite subr0.
Qed.

Lemma poly_size_mull : forall p q, p != (0 : {poly F}) -> (size q <= size (p * q)%R)%N.
Proof.
move=> p q p0.
case q0: (q == 0); first by rewrite (eqP q0) mulr0 size_poly0 leqnn.
rewrite size_mul_id=> //; last by rewrite q0.
rewrite -ltnS prednK; first by rewrite -subn_gt0 addnK lt0n size_poly_eq0.
by rewrite addn_gt0 lt0n size_poly_eq0 p0.
Qed.

Definition poly_euclidMixin := EuclideanRing.Mixin poly_size_mull edivP.

Definition poly_dvdMixin := EuclidDvdMixin {poly F} poly_euclidMixin.
Canonical Structure poly_dvdRingType := DvdRingType {poly F} poly_dvdMixin.

Definition poly_gcdMixin := EuclidGcdMixin {poly F} poly_euclidMixin.
Canonical Structure poly_gcdType := GcdRingType {poly F} poly_gcdMixin.

Definition poly_bezoutMixin := EuclidBezoutMixin {poly F} poly_euclidMixin.
Canonical Structure poly_bezoutType := BezoutRingType {poly F} poly_bezoutMixin.

Definition poly_priMixin := EuclidPriMixin {poly F} poly_euclidMixin.
Canonical Structure poly_priType := PriRingType {poly F} poly_priMixin.

Canonical Structure poly_euclidType := EuclidRingType {poly F} poly_euclidMixin.

End PolyPriField.
End PolyPriField.
