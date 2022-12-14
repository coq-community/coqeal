From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_real_closed.
From CoqEAL Require Import ssrcomplements.

(******************************************************************************)
(*                                                                            *)
(*  This file contains theory about polynomials with coefficients             *)
(*  in a closed field.                                                        *)
(*                                                                            *)
(*  In follow we pose p = (X - r1)^+a1 * (X - r2)^+a2 * ... * (X - rn)^+an    *)
(*                                                                            *)
(*            root_seq p == the sequence of all roots of polynomial p.        *)
(*       root_seq_uniq p == the sequence of all distinct roots of             *)
(*                          polynomial p (i.e the sequence [:: r1; ...; rn])  *)
(*         root_mu_seq p == the sequence of pair off the roots and            *)
(*                          its multiplicity of polynomial p.                 *)
(*                          (i.e the sequence [:: (r1,a1); ... ; (rn,an)])    *)
(*       root_seq_poly s == the concatenation of the sequences root_mu_seq p  *)
(*                          for all polynomials p in the sequence s.          *)
(*   linear_factor_seq p == the sequence of linear factor tha appear of the   *)
(*                          decompositionof polynomial p. (i.e the sequence   *)
(*                          [:: (X - r1)^+a1; ... ; (X - rn)^+an])            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section poly_closedFieldType.

Variable F : closedFieldType.
Import GRing.Theory.

Local Open Scope ring_scope.

Definition root_seq : {poly F} -> seq F :=
  let fix loop (p : {poly F}) (n : nat) :=
    if n is n.+1 then
      if (size p != 1%N) =P true is ReflectT p_neq0
        then let x := projT1 (sigW (closed_rootP p p_neq0)) in
          x :: loop (p %/ ('X - x%:P)) n
        else [::]
      else [::]
  in fun p => loop p (size p).

Lemma root_root_seq (p : {poly F}) x : p != 0 -> x \in root_seq p = root p x.
Proof.
rewrite /root_seq; set loop := fix loop p n := if n is _.+1 then _ else _.
elim: size {-2 5}p (erefl (size p))=> /= {p} [|n ihn] p /=.
  by move/eqP; rewrite size_poly_eq0 => /eqP->; rewrite eqxx.
case: eqP=> /= [sp_neq1 sp_eqn|/negP]; last first.
  rewrite negbK=> /size_poly1P [c c_neq0 ->] _ _.
  by rewrite rootC (negPf c_neq0).
case: sigW => z /= rpz p_neq0.
rewrite in_cons; have [->|neq_xz] //= := altP eqP.
move: rpz sp_eqn => /factor_theorem [q ->].
rewrite mulpK ?polyXsubC_eq0 // rootM root_XsubC (negPf neq_xz) orbF.
have [->|q_neq0] := eqVneq q 0; first by rewrite mul0r size_poly0.
rewrite size_mul ?polyXsubC_eq0 // size_XsubC addn2.
by case=> /ihn /(_ q_neq0).
Qed.

Lemma root_seq_cons (p : {poly F}) x s : root_seq p = x :: s ->
  s = root_seq (p %/ ('X - x%:P)).
Proof.
rewrite /root_seq; set loop := fix loop p n := if n is _.+1 then _ else _.
case H: (size p)=> [|n] //=; case: eqP=> // Hp.
move/eqP; rewrite eqseq_cons; case/andP=> /eqP {1}<- /eqP <-.
suff ->: n = size (p %/ ('X - x%:P))=> //.
by rewrite size_divp ?polyXsubC_eq0 // size_XsubC subn1 H.
Qed.

Lemma root_seq_eq (p : {poly F}) :
  p = lead_coef p *: \prod_(x <- root_seq p) ('X - x%:P).
Proof.
move: {2}(root_seq p) (erefl (root_seq p))=> s.
elim: s p=> [p | x s IHp p H].
  rewrite /root_seq; set loop := fix loop p n := if n is _.+1 then _ else _.
  case H: (size p)=> [|n].
    move/eqP: H; rewrite size_poly_eq0=> /eqP ->.
    by rewrite lead_coef0 scale0r.
  case: n H => [H | n H] /=; case: eqP => //.
    move=> _ _; rewrite big_nil.
    move/eqP: H => /size_poly1P [c H] ->.
    by rewrite lead_coefC alg_polyC.
  by move/negP; rewrite negbK H.
rewrite H big_cons (root_seq_cons H) mulrC scalerAl.
have Hfp : p = p %/ ('X - x%:P) * ('X - x%:P).
  apply/eqP; rewrite -dvdp_eq dvdp_XsubCl -root_root_seq.
    by rewrite H mem_head.
  move: H; rewrite /root_seq.
  set loop := fix loop p n := if n is _.+1 then _ else _.
  by apply: contraPneq => ->; rewrite size_poly0.
suff -> : lead_coef p = lead_coef (p %/ ('X - x%:P)).
  by rewrite -IHp ?(root_seq_cons H).
by rewrite {1}Hfp lead_coef_Mmonic // monicXsubC.
Qed.

Lemma root_seq0 : root_seq 0 = [::].
Proof. by rewrite /root_seq size_poly0. Qed.

Lemma size_root_seq p : size (root_seq p) = (size p).-1.
Proof.
have [-> | p0] := eqVneq p 0; first by rewrite root_seq0 size_poly0.
rewrite {2}[p]root_seq_eq size_scale ?lead_coef_eq0 //.
rewrite (big_nth 0) big_mkord size_prod.
  rewrite (eq_bigr (fun=> (1 + 1)%N)).
    by rewrite big_split sum1_card /= subSKn addnK card_ord.
  by move=> i _; rewrite size_XsubC.
by move=> i _; rewrite polyXsubC_eq0.
Qed.

Lemma root_seq_nil (p : {poly F}) :
  (size p <= 1)%N = ((root_seq p) == [::]).
Proof. by rewrite -subn_eq0 subn1 -size_root_seq size_eq0. Qed.

Lemma sub_root_div (p q : {poly F}) (Hq : q != 0) :
  p %| q -> {subset (root_seq p) <= (root_seq q)} .
Proof.
case: (eqVneq p 0) => [->|p0]; first by rewrite root_seq0.
by case/dvdpP => x Hx y; rewrite !root_root_seq // Hx rootM orbC=> ->.
Qed.

Definition root_seq_uniq p := undup (root_seq p).

Lemma prod_XsubC_count (p : {poly F}):
   p = (lead_coef p) *:
   \prod_(x <- root_seq_uniq p) ('X - x%:P)^+ (count_mem x (root_seq p)).
Proof.
by rewrite {1}[p]root_seq_eq (prod_seq_count (root_seq p)).
Qed.

Lemma count_root_seq p x : count_mem x (root_seq p) = \mu_x p.
Proof.
have [-> | Hp] := eqVneq p 0; first by rewrite root_seq0 mu0.
apply/eqP; rewrite -muP //.
case/boolP: (x \in root_seq p) => [|H].
  rewrite -mem_undup => H.
  move: (prod_XsubC_count p).
  rewrite (bigD1_seq x) //= ?undup_uniq //.
  set b:= \big[_/_]_(_ <- _ | _) _ => Hpq.
  apply/andP; split; apply/dvdpP.
    by exists (lead_coef p *: b); rewrite -scalerAl mulrC.
  case=> q Hq.
  have H1: ~~ (('X - x%:P) %| b).
    rewrite dvdp_XsubCl; apply/rootP.
    rewrite horner_prod; apply/eqP.
    rewrite (big_nth 0) big_mkord.
    apply/prodf_neq0=> i Hix.
    by rewrite horner_exp hornerXsubC expf_neq0 // subr_eq0 eq_sym.
  have H2: (('X - x%:P) %| b).
    apply/dvdpP; exists ((lead_coef p)^-1 *: q).
    apply: (@scalerI _ _ (lead_coef p)); first by rewrite lead_coef_eq0.
    rewrite -scalerAl scalerA mulrV ?unitfE ?lead_coef_eq0 // scale1r.
    have HX: (('X - x%:P)^+ (count_mem x (root_seq p))) != 0.
      by apply: expf_neq0; rewrite -size_poly_eq0 size_XsubC.
    rewrite -(mulpK (_ *: b) HX) -(mulpK (q * _) HX).
    by rewrite -scalerAl mulrC -Hpq -mulrA -exprS -Hq.
  by rewrite H2 in H1.
have->: count_mem x (root_seq p) = 0%N by apply/count_memPn.
by rewrite dvd1p /= dvdp_XsubCl -root_root_seq.
Qed.

Definition root_mu_seq p := [seq (x,(\mu_x p)) | x <- (root_seq_uniq p)].

Lemma root_mu_seq_pos x p : p != 0 -> x \in root_mu_seq p -> (0 < x.2)%N.
Proof.
move=> Hp H.
have Hr: size (root_seq_uniq p) = size (root_mu_seq p) by rewrite size_map.
have Hs: (index x (root_mu_seq p) < size (root_seq_uniq p))%N.
  by rewrite Hr index_mem.
rewrite -(nth_index (0,0%N) H) // (nth_map 0) // mu_gt0 //.
by rewrite -root_root_seq // -mem_undup mem_nth.
Qed.

Definition root_seq_poly (s : seq {poly F}) := flatten (map root_mu_seq s).

Lemma root_seq_poly_pos x s : (forall p , p \in s -> p !=0) ->
  x \in root_seq_poly s -> (0 < x.2)%N.
Proof.
elim : s=> [|p l IHl H]; first by rewrite in_nil.
rewrite mem_cat.
case/orP; first by apply: root_mu_seq_pos; apply: H; rewrite mem_head.
by apply: IHl=> q Hq; apply: H; rewrite in_cons Hq orbT.
Qed.

Definition linear_factor_seq p :=
   [seq ('X - x.1%:P)^+x.2 | x <- (root_mu_seq p)].

Lemma monic_linear_factor_seq p : forall q, q \in linear_factor_seq p ->
  q \is monic.
Proof.
move=> q Hq; rewrite -(nth_index 0 Hq) (nth_map (0,0%N)).
apply: monic_exp; first by apply: monicXsubC.
by rewrite -index_mem size_map in Hq.
Qed.

Lemma size_linear_factor_leq1 p : forall q, q \in linear_factor_seq p ->
  (1 < size q)%N.
Proof.
move=> q; have [-> | Hp Hq] := eqVneq p 0.
  rewrite /linear_factor_seq /root_mu_seq.
  by rewrite /root_seq_uniq /root_seq size_poly0.
rewrite -(nth_index 0 Hq) (nth_map (0,0%N)); last first.
  by rewrite -index_mem size_map in Hq.
rewrite size_exp_XsubC (nth_map 0); last first.
  by rewrite -index_mem !size_map in Hq.
rewrite -(@prednK (\mu_ _ _)) // mu_gt0 // -root_root_seq //.
rewrite -mem_undup mem_nth //.
by rewrite -index_mem !size_map in Hq.
Qed.

Lemma coprimep_linear_factor_seq p :
  forall (i j : 'I_(size (linear_factor_seq p))),
  i != j ->
  coprimep (linear_factor_seq p)`_i (linear_factor_seq p)`_j.
Proof.
move=> [i +] [j +]; rewrite !size_map=> Hi Hj Hij.
rewrite !(nth_map (0,0%N)) ?size_map //.
apply/coprimep_expl/coprimep_expr/coprimep_factor.
by rewrite unitfE subr_eq0 !(nth_map 0) //= nth_uniq // ?undup_uniq // eq_sym.
Qed.

Lemma prod_XsubC_mu (p : {poly F}):
   p = (lead_coef p) *: \prod_(x <- root_seq_uniq p) ('X - x%:P)^+(\mu_x p).
Proof.
rewrite {1}[p]prod_XsubC_count.
by congr GRing.scale; apply: eq_bigr => i _; rewrite count_root_seq.
Qed.

Lemma monic_prod_XsubC p :
   p \is monic -> p = \prod_(x <- root_seq_uniq p) ('X - x%:P)^+(\mu_x p).
Proof.
by move/monicP=> H; rewrite {1}[p]prod_XsubC_mu H scale1r.
Qed.

Lemma prod_factor (p : {poly F}):
   p = (lead_coef p) *: \prod_(x <- linear_factor_seq p) x.
Proof.
by rewrite !big_map {1}[p]prod_XsubC_mu.
Qed.

Lemma monic_prod_factor p :
   p \is monic -> p = \prod_(x <- linear_factor_seq p) x.
Proof.
by move/monicP=> H; rewrite {1}[p]prod_factor H scale1r.
Qed.

Lemma uniq_root_mu_seq (p : {poly F}) : uniq (root_seq p) ->
  forall x, x \in root_mu_seq p -> x.2 = 1%N.
Proof.
move=> H x /(nthP (0,0%N)) [] i; rewrite size_map=> Hi.
rewrite (nth_map 0) // => <- /=; move: Hi.
rewrite /root_seq_uniq undup_id // -count_root_seq => Hi.
by rewrite count_uniq_mem // (mem_nth 0 Hi).
Qed.

Lemma uniq_root_dvdp p q : q != 0 ->
  (uniq (root_seq q)) -> p %| q -> (uniq (root_seq p)).
Proof.
move=> Hq Hq2 Hpq.
apply: count_mem_uniq=> x.
have Hc:= count_uniq_mem x Hq2.
have Hle: (count_mem x (root_seq p) <= count_mem x (root_seq q))%N.
  rewrite !count_root_seq; case/dvdpP: Hpq => r Hr.
  by rewrite Hr mu_mul -?Hr // leq_addl.
have: (count_mem x (root_seq p) <= 1)%N.
  by rewrite (leq_trans Hle) // Hc; case: (x \in root_seq q).
rewrite leq_eqVlt ltnS leqn0.
case Hp: (x \in root_seq p).
  rewrite -has_pred1 has_count in Hp.
  by rewrite (eqn_leq _ 0%N) leqNgt Hp orbF => /eqP ->.
by rewrite eqn_leq -has_count has_pred1 Hp andbF orFb => /eqP ->.
Qed.

Lemma root_root_mu_seq p : [seq x.1 | x <- root_mu_seq p] = root_seq_uniq p.
Proof.
apply: (@eq_from_nth _ 0)=>[|i]; rewrite !size_map //.
by move=> Hi; rewrite (nth_map (0,0%N)) ?size_map // (nth_map 0) //.
Qed.

End poly_closedFieldType.
