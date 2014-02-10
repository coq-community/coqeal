(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype finfun perm matrix bigop zmodp mxalgebra.
Require Import choice poly polydiv mxpoly binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

(** This file contains definitions and lemmas that are generic enough that
we could try to integrate them in Math Components' library.
Definitions and theories are gathered according to the file of the
library which they could be moved to. *)

(* Cyril : I should push these in ssr someday *)
Section extraPP.

Lemma existsPP (T : finType) (P : T -> Prop) (b : pred T) :
   (forall x, reflect (P x) (b x)) ->
   reflect (exists x : T, P x) [exists x, b x].
Proof. by move=> bP; apply: (iffP existsP) => [] [Px /bP]; exists Px. Qed.

Lemma forallPP (T : finType) (P : T -> Prop) (b : pred T) :
   (forall x, reflect (P x) (b x)) ->
   reflect (forall x : T, P x) [forall x, b x].
Proof. by move=> bP; apply: (iffP forallP) => [] hP x; apply/bP. Qed.

End extraPP.

Notation "\forall_ view" := (forallPP (fun _ => view)) (at level 0).
Notation "\exists_ view" := (existsPP (fun _ => view)) (at level 0).

(********************* seq.v *********************)
Section Seq.

Variables (T1 T2 T3 : Type) (f : T1 -> T2 -> T3).

Lemma seq2_ind (P : seq T1 -> seq T2 -> Prop) : P [::] [::] ->
 (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
  forall s1 s2, size s1 = size s2 -> P s1 s2.
Proof.
move=> Pnil Pcons.
elim=> [|x1 l1 IH1]; case=> // x2 l2 /eqnP /= Hs.
by apply/Pcons/IH1/eqnP.
Qed.

End Seq.

(******************** bigop.v ********************)
Section BigOp.

Import GRing.Theory.

Variable R : comRingType.
Variable T : eqType.

Open Scope ring_scope.

(*** This lemma is usefull to prove that \mu_x p = count (xpred1 x) s where 
     s is the sequence of roots of polynomial p ***)
Lemma prod_seq_count (s : seq T) (F : T -> R) :
  \prod_(i <- s) F i =
  \prod_(i <- (undup s)) ((F i) ^+ (count (xpred1 i) s)).
Proof.
elim: s=> /= [|a l IHl]; first by rewrite !big_nil.
rewrite big_cons IHl.
set r:= if _ then _ else _.
have ->: \big[*%R/1]_(i <- r) (F i) ^+ ((a == i) + count (eq_op^~ i) l) =
         \big[*%R/1]_(i <- r) (F i) ^+ (a == i) *
         \big[*%R/1]_(i <- r) (F i) ^+ (count (eq_op^~ i) l).
  by rewrite -big_split /=; apply: eq_bigr=> i _; rewrite exprD.
have ->: \big[*%R/1]_(i <- r) (F i) ^+ (a == i) = F a.
  rewrite /r; case: ifP=>[|notal].
    rewrite -mem_undup=> aundl.
    rewrite (bigD1_seq _ aundl (undup_uniq l)) /= eqxx big1 ?mulr1 //.
    by move=> i /negbTE neqai; rewrite eq_sym neqai.
  rewrite big_cons eqxx big1_seq ?mulr1 // => i /= iundl.
  case eqai: (a == i)=> //.
  by rewrite (eqP eqai) -mem_undup iundl in notal.
rewrite /r; case: ifP=> // /negbT notal.
rewrite big_cons.
have->: count (xpred1 a) l = 0%N.
  by apply/eqP; rewrite -leqn0 leqNgt -has_count has_pred1.
by rewrite mul1r.
Qed.

End BigOp.

(********************* matrix.v *********************)
Section Matrix.

Local Open Scope ring_scope.
Import GRing.Theory.

Section matrix_raw_type.

Variable T : Type.

Lemma row_thin_mx  p q (M : 'M_(p,0)) (N : 'M[T]_(p,q)) :
  row_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP=> [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

Lemma col_flat_mx p q (M : 'M[T]_(0, q)) (N : 'M_(p,q)) :
  col_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP => [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

End matrix_raw_type.

Section matrix_ringType.

Variable R : ringType.

Lemma mulmx_rsub m n p k (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p + k)) :
  A *m rsubmx B = (rsubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma mulmx_lsub m n p k (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p + k)) :
  A *m lsubmx B = (lsubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma col_0mx m n (M : 'M[R]_(m, n)) : col_mx (0 :'M_(0%N, _)) M = M.
Proof.
apply/matrixP=> i j; rewrite !mxE.
case: splitP => [[] //|k eq_i_k]; congr (M _ _).
by apply: val_inj; rewrite /= eq_i_k.
Qed.

Lemma col_id_mulmx m n (M : 'M[R]_(m,n)) i :
  M *m col i 1%:M = col i M.
Proof.
apply/matrixP=> k l; rewrite !mxE.
rewrite (bigD1 i) // big1 /= ?addr0 ?mxE ?eqxx ?mulr1 // => j /negbTE neqji.
by rewrite !mxE neqji mulr0.
Qed.

Lemma row_id_mulmx m n (M : 'M[R]_(m,n)) i :
   row i 1%:M *m M = row i M.
Proof.
apply/matrixP=> k l; rewrite !mxE.
rewrite (bigD1 i) // big1 /= ?addr0 ?mxE ?eqxx ?mul1r // => j /negbTE Hj.
by rewrite !mxE eq_sym Hj mul0r.
Qed.

Lemma row'_col'_char_poly_mx m i (M : 'M[R]_m) :
  row' i (col' i (char_poly_mx M)) = char_poly_mx (row' i (col' i M)).
Proof.
apply/matrixP=> k l; rewrite !mxE.
suff ->: (lift i k == lift i l) = (k == l) => //.
by apply/inj_eq/lift_inj.
Qed.

Lemma exp_block_mx m n (A: 'M[R]_m.+1) (B : 'M_n.+1) k :
  (block_mx A 0 0 B) ^+ k = block_mx (A ^+ k) 0 0 (B ^+ k).
Proof.
elim: k=> [|k IHk].
  by rewrite !expr0 -scalar_mx_block.
rewrite !exprS IHk /GRing.mul /= (mulmx_block A 0 0 B (A ^+ k)).
by rewrite !mulmx0 !mul0mx !add0r !addr0.
Qed.

Lemma char_block_mx m n (A : 'M[R]_m) (B : 'M[R]_n) :
  char_poly_mx (block_mx A 0 0 B) =
  block_mx (char_poly_mx A) 0 0 (char_poly_mx B).
Proof.
apply/matrixP=> i j; rewrite !mxE.
case: splitP=> k Hk; rewrite !mxE; case: splitP=> l Hl; rewrite !mxE;
rewrite -!(inj_eq (@ord_inj _)) Hk Hl ?subr0 ?eqn_add2l //.
  by rewrite ltn_eqF // ltn_addr.
by rewrite gtn_eqF // ltn_addr.
Qed.

End matrix_ringType.

Section matrix_comUnitRingType.

Variable R : comUnitRingType.

Lemma invmx_block n1 n2  (Aul : 'M[R]_n1.+1) (Adr : 'M[R]_n2.+1) :
   (block_mx Aul 0 0 Adr) \in unitmx ->
  (block_mx Aul 0 0 Adr)^-1 = block_mx Aul^-1 0 0 Adr^-1.
Proof.
move=> Hu.
have Hu2: (block_mx Aul 0 0 Adr) \is a GRing.unit by [].
rewrite unitmxE det_ublock unitrM in Hu.
case/andP: Hu; rewrite -!unitmxE => HAul HAur.
have H: block_mx Aul 0 0 Adr *  block_mx Aul^-1 0 0 Adr^-1 = 1.
  rewrite /GRing.mul /= (mulmx_block Aul _ _ _ Aul^-1) !mulmxV //.
  by rewrite !mul0mx !mulmx0 !add0r addr0 -scalar_mx_block.
by apply: (mulrI Hu2); rewrite H mulrV.
Qed.

End matrix_comUnitRingType.

End Matrix.

Section Poly.

Variable R : idomainType.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma coprimep_factor (a b : R) : (b - a)%R \is a GRing.unit ->
   coprimep ('X - a%:P) ('X - b%:P).
Proof.
move=> Hab; apply/Bezout_coprimepP.
exists ((b - a)^-1%:P , -(b - a) ^-1%:P).
rewrite /= !mulrBr !mulNr opprK -!addrA (addrC (- _)) !addrA addrN.
by rewrite add0r -mulrBr -rmorphB -rmorphM mulVr // eqpxx.
Qed.

End Poly.

(****************************************************************************)
(****************************************************************************)
(************ left pseudo division, it is complement of polydiv. ************)
(****************************************************************************)
(****************************************************************************)
Import GRing.Theory.
Import Pdiv.Ring.
Import Pdiv.RingMonic.

Local Open Scope ring_scope.

Module RPdiv.

Section RingPseudoDivision.

Variable R : ringType.
Implicit Types d p q r : {poly R}.

Definition id_converse_def := (fun x : R => x : R^c).
Lemma add_id : additive id_converse_def.
Proof. by []. Qed.

Definition id_converse := Additive add_id.

Lemma expr_rev (x : R) k : (x : R^c) ^+ k = x ^+ k.
Proof. by elim:k=> // k IHk; rewrite exprS exprSr IHk. Qed.

Definition phi (p : {poly R}^c) := map_poly id_converse p.

Fact phi_is_rmorphism : rmorphism phi.
Proof.
split=> //; first exact:raddfB.
split=> [p q|]; apply/polyP=> i; last by rewrite coef_map !coef1.
by rewrite coefMr coef_map coefM; apply: eq_bigr => j _; rewrite !coef_map.
Qed.

Canonical phi_rmorphism := RMorphism phi_is_rmorphism.

Definition phi_inv (p : {poly R^c}) :=
  map_poly (fun x : R^c => x : R) p : {poly R}^c.

Lemma phiK : cancel phi phi_inv.
Proof. by move=> p; rewrite /phi_inv -map_poly_comp_id0 // map_poly_id. Qed.

Lemma phi_invK : cancel phi_inv phi.
Proof. by move=> p; rewrite /phi -map_poly_comp_id0 // map_poly_id. Qed.

Lemma phi_bij : bijective phi.
Proof. by exists phi_inv; first exact: phiK; exact: phi_invK. Qed.

Lemma monic_map_inj (aR rR : ringType) (f : aR -> rR) (p : {poly aR}) :
  injective f -> f 0 = 0 -> f 1 = 1 -> map_poly f p \is monic = (p \is monic).
Proof.
move=> inj_f eq_f00 eq_f11; rewrite !monicE lead_coef_map_inj ?rmorph0 //.
by rewrite -eq_f11 inj_eq.
Qed.

Definition redivp_l (p q : {poly R}) : nat * {poly R} * {poly R} :=
  let:(d,q,p) := (redivp (phi p) (phi q)) in
  (d, phi_inv q, phi_inv p).

Definition rdivp_l p q := ((redivp_l p q).1).2.
Definition rmodp_l p q := (redivp_l p q).2.
Definition rscalp_l p q := ((redivp_l p q).1).1.
Definition rdvdp_l p q := rmodp_l q p == 0.
Definition rmultp_l := [rel m d | rdvdp_l d m].

Lemma ltn_rmodp_l p q : (size (rmodp_l p q) < size q) = (q != 0).
Proof.
have := ltn_rmodp (phi p) (phi q).
rewrite -(rmorph0 phi_rmorphism) (inj_eq (can_inj phiK)) => <-.
rewrite /rmodp_l /redivp_l /rmodp; case: (redivp _ _)=> [[k q'] r'] /=.
by rewrite !size_map_inj_poly.
Qed.

End RingPseudoDivision.

Module mon.

Section MonicDivisor.

Variable R : ringType.
Implicit Types p q r : {poly R}.

Variable d : {poly R}.
Hypothesis mond : d \is monic.

Lemma rdivp_l_eq p :
  p = d * (rdivp_l p d) + (rmodp_l p d).
Proof.
have mon_phi_d: phi d \is monic by rewrite monic_map_inj.
apply:(can_inj (@phiK R)); rewrite {1}[phi p](rdivp_eq mon_phi_d) rmorphD.
rewrite rmorphM /rdivp_l /rmodp_l /redivp_l /rdivp /rmodp.
by case: (redivp _ _)=> [[k q'] r'] /=; rewrite !phi_invK.
Qed.

End MonicDivisor.

End mon.

End RPdiv.

(****************************************************************************)
(****************************************************************************)
(****************************************************************************)
(****************************************************************************)
