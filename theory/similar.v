(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype finfun ssrnat seq.
From mathcomp Require Import choice ssralg poly polydiv mxpoly matrix bigop.
From mathcomp Require Import mxalgebra perm fingroup tuple.
Require Import mxstructure dvdring.

(**   This file contains the definitions of similarity and equivalence
      between two matrices, and the proofs of some properties about
      these notions.

            similar M N == The matrices M and N are similar.
         equivalent M N == The matrices M and N are equivalent.

                                                                              *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section complements.

Lemma seq2_ind (T1 T2 : Type) (P : seq T1 -> seq T2 -> Prop) : P [::] [::] ->
 (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
  forall s1 s2, size s1 = size s2 -> P s1 s2.
Proof.
move=> HP IHP.
elim=> [|x1 l1 IH1]; case=> // x2 l2 /= Hs.
apply: IHP; apply: IH1.
by move/eqnP: Hs=> /= /eqnP.
Qed.
End complements.

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

HB.instance Definition _ := GRing.isAdditive.Build R R^c id_converse_def add_id.
Definition id_converse : {additive _ -> _} := id_converse_def.

Lemma expr_rev (x : R) k : (x : R^c) ^+ k = x ^+ k.
Proof. by elim:k=> // k IHk; rewrite exprS exprSr IHk. Qed.

Definition phi (p : {poly R}^c) := map_poly id_converse p.

Fact phi_is_rmorphism : multiplicative phi.
Proof.
split=> [p q|]; apply/polyP=> i; last by rewrite coef_map !coef1.
by rewrite coefMr coef_map coefM; apply: eq_bigr => j _; rewrite !coef_map.
Qed.

HB.instance Definition _ := GRing.Additive.copy phi phi.
HB.instance Definition _ := GRing.isMultiplicative.Build _ _ _ phi_is_rmorphism.

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
rewrite -(rmorph0 phi) (inj_eq (can_inj phiK)) => <-.
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
apply: (can_inj (@phiK R)); rewrite {1}[phi p](rdivp_eq mon_phi_d) rmorphD.
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




Section SimilarDef.

Local Open Scope ring_scope.
Import GRing.Theory.
Variable R : comUnitRingType.

Definition similar m n (A : 'M[R]_m) (B : 'M[R]_n) :=
   m = n /\ exists2 P, P \in unitmx & P *m A = (conform_mx P B) *m P.

Lemma similar0 m (A : 'M[R]_0) (B : 'M[R]_m) : (0 = m)%N -> similar A B.
Proof.
move=> H; split=> //.
exists 1%:M; first exact: unitmx1.
by apply/matrixP; case.
Qed.

Lemma similar_sym m : forall n (A : 'M[R]_m) (B : 'M[R]_n),
  similar A B -> similar B A.
Proof.
case=> [A B [H1 H2]|n A B [Hmn]].
  by apply: similar0; rewrite H1.
move: A; rewrite Hmn => A [P HP HPA].
split=> //; exists P^-1; first by rewrite unitmx_inv.
rewrite !conform_mx_id -1?[A *m _]mul1mx -?(mulVmx HP) in HPA *.
by rewrite mulmxA -(mulmxA P^-1) HPA -!mulmxA mulmxV // mulmx1.
Qed.

Lemma similar_trans m n p (B : 'M[R]_n) (A : 'M[R]_m) (C : 'M[R]_p) :
  similar A B -> similar B C -> similar A C.
Proof.
case=> [Hmn HAB] [Hnp].
move: Hmn Hnp A B C HAB=> -> -> A B C [P HP HAB] [Q HQ HBC].
split=> //; exists (Q *m P); first by rewrite unitmx_mul HP HQ.
by rewrite -mulmxA HAB !conform_mx_id !mulmxA HBC conform_mx_id.
Qed.

Lemma similar_refl n (A : 'M[R]_n) : similar A A.
Proof.
split=> //; exists 1%:M; first by rewrite unitmx1.
by rewrite conform_mx_id mulmx1 mul1mx.
Qed.

Lemma similar_det m n (A : 'M[R]_m) (B : 'M[R]_n) :
  similar A B -> \det A = \det B.
Proof.
case=> [Hmn]; move: Hmn A B=> -> A B [P HP HAB].
apply: (@mulrI _ (\det P)); first by rewrite -unitmxE.
by rewrite -det_mulmx mulrC -det_mulmx HAB conform_mx_id.
Qed.

Lemma similar_cast n m p (eq1 : m = p) (eq2 : m = p)
  (A : 'M[R]_n) (B : 'M[R]_m) :
  similar A (castmx (eq1,eq2) B) <-> similar A B.
Proof. by case: _ /eq1 eq2=> eq2; rewrite castmx_id. Qed.

Lemma similar_diag_mx_seq m n s1 s2 :
  m = n -> size s1 = m -> perm_eq s1 s2 ->
similar (diag_mx_seq m m s1) (diag_mx_seq n n s2).
Proof.
move=> eq Hms Hp.
have Hs12:= perm_size Hp.
have Hs2: size s2 == n by rewrite -Hs12 Hms eq.
pose t:= Tuple Hs2.
have HE: s2 = t by [].
move: Hp; rewrite HE.
case/tuple_permP=> p Hp.
split=> //; rewrite eq.
exists (perm_mx p)^T; first by rewrite unitmx_tr unitmx_perm.
apply/matrixP=> i j; rewrite conform_mx_id !mxE (bigD1 j) //= big1 ?addr0.
  rewrite (bigD1 i) //= big1 ?addr0.
    rewrite !mxE Hp -tnth_nth tnth_mktuple (tnth_nth 0) HE !eqxx.
    case: (p j == i) /eqP => Hij; first by rewrite Hij mulr1 mul1r.
    by rewrite mulr0 mul0r.
  by move=> k /negbTE Hk; rewrite !mxE eq_sym (inj_eq (@ord_inj _)) Hk mul0r.
by move=> k /negbTE Hk; rewrite !mxE (inj_eq (@ord_inj _)) Hk mulr0.
Qed.


Lemma similar_ulblockmx n1 n2 n3 (Aul : 'M[R]_n1) (Adr : 'M[R]_n3)
  (Bul : 'M[R]_n2) :
  similar Aul Bul ->
  similar (block_mx Aul 0 0 Adr) (block_mx Bul 0 0 Adr).
Proof.
case=> Hn1 [P HP HAB].
have Hu : (block_mx P 0 0 1%:M) \in unitmx.
  by move=> n; rewrite unitmxE det_ublock det1 mulr1 -unitmxE.
split; first by rewrite Hn1.
move: Aul P HP HAB Hu; rewrite Hn1=> Aul P HP; rewrite conform_mx_id=> HAB Hu.
exists (block_mx P 0 0 1%:M); first exact: Hu.
rewrite conform_mx_id !mulmx_block !mul0mx !mulmx0.
by rewrite !add0r !addr0 mulmx1 mul1mx HAB.
Qed.

Lemma similar_drblockmx n1 n2 n3(Aul : 'M[R]_n1) (Adr : 'M[R]_n2)
  (Bdr : 'M[R]_n3) :
  similar Adr Bdr ->
  similar (block_mx Aul 0 0 Adr) (block_mx Aul 0 0 Bdr).
Proof.
case=> Hn2 [P HP HAB].
have Hu : (block_mx 1%:M 0 0 P) \in unitmx.
  by move=> n; rewrite unitmxE det_ublock det1 mul1r -unitmxE.
split; first by rewrite Hn2.
move: Adr P HP HAB Hu; rewrite Hn2=> Adr P HP; rewrite conform_mx_id=> HAB Hu.
exists (block_mx 1%:M 0 0 P); first exact: Hu.
rewrite conform_mx_id !mulmx_block !mul0mx !mulmx0.
by rewrite !add0r !addr0 mulmx1 mul1mx HAB.
Qed.

Lemma similar_dgblockmx n1 n2 n3 n4 (Aul : 'M[R]_n1) (Adr : 'M[R]_n2)
  (Bul : 'M[R]_n3) (Bdr : 'M[R]_n4) :
  similar Aul Bul -> similar Adr Bdr ->
  similar (block_mx Aul 0 0 Adr) (block_mx Bul 0 0 Bdr).
Proof.
move=> HABu HABd; apply: (similar_trans (B:= (block_mx Bul 0 0 Adr))).
  exact: similar_ulblockmx.
exact: similar_drblockmx.
Qed.

Lemma similar_exp m n (A : 'M[R]_m.+1) (B : 'M_n.+1) k:
  similar A B -> similar (A ^+ k) (B ^+ k).
Proof.
case=> /eqP; rewrite eqSS=> /eqP eq [P HP]; move: B.
rewrite /similar -eq=> B; rewrite conform_mx_id=> HAB.
split=> //; exists P => //; rewrite conform_mx_id.
elim: k=> [|k IHk].
  by rewrite !expr0 mulmx1 mul1mx.
by rewrite exprSr mulmxA IHk -mulmxA HAB exprSr mulmxA.
Qed.

Lemma similar_poly  m n (A : 'M[R]_m.+1) (B : 'M_n.+1) p:
  similar A B -> similar (horner_mx A p) (horner_mx B p).
Proof.
case=> /eqP; rewrite eqSS=> /eqP eq [P HP]; move: B.
rewrite /similar -eq=> B; rewrite conform_mx_id=> HAB.
split=> //; exists P => //; rewrite conform_mx_id.
elim/poly_ind: p=>[|p c IHp].
  by rewrite !rmorph0 mulmx0 mul0mx.
rewrite !rmorphD !rmorphM /= !horner_mx_X !horner_mx_C.
by rewrite mulmxDr mulmxDl mulmxA IHp -mulmxA HAB mulmxA scalar_mxC.
Qed.

Lemma similar_horner n m (A : 'M[R]_n.+1) (B : 'M_m.+1) p :
  similar A B -> horner_mx A p = 0 -> horner_mx B p = 0.
Proof.
move/(similar_poly p)=> HAB HhA; move: HAB; rewrite HhA.
case=> /eqP; rewrite eqSS=> /eqP eq [P HP].
rewrite -eq in B *; rewrite conform_mx_id mulmx0=> H.
by apply: (mulIr HP); rewrite mul0r.
Qed.

Lemma similar_diag_block : forall l1 l2, size l1 = size l2 ->
   forall (F1 F2 : forall n : nat, nat -> 'M[R]_n.+1),
   (forall i, i < size l1 ->
    similar (F1 (nth 0%N l1 i) i) (F2 (nth 0%N l2 i) i)) ->
   similar (diag_block_mx l1 F1) (diag_block_mx l2 F2).
Proof.
case=>[|a l1]; case=> //=.
  by move=> *; apply: similar_refl.
move=> b l2 /eqP; rewrite eqSS=> /eqP Hsl F1 F2 Hl.
have Hab: similar (F1 a 0%N) (F2 b 0%N) by exact: (Hl 0%N).
move: l1 l2 Hsl a b F1 F2 Hab Hl.
apply: seq2_ind=> //= x1 x2 l1 l2 IH a b F1 F2 Hab H.
apply: (similar_dgblockmx Hab).
apply: IH=>[|i]; first exact: (H 1%N).
exact: (H i.+1).
Qed.

End SimilarDef.

Section EquivalentDef.

Variable R : comUnitRingType.
Local Open Scope ring_scope.
Import GRing.Theory.

Definition equivalent m1 n1 m2 n2 (A : 'M[R]_(m1,n1)) (B : 'M[R]_(m2,n2)) :=
  [/\ m1 = m2, n1 = n2 & exists M N,
  [/\ M \in unitmx, N \in unitmx & M *m A *m N = conform_mx A B]].

Lemma equiv0l n m p (A : 'M[R]_(0,n)) (B : 'M[R]_(m,p)) :
 (0 = m)%N -> (n = p)%N ->  equivalent A B.
Proof.
move=> eq1 eq2; split=> //.
exists 1%:M, 1%:M; split; try exact: unitmx1.
by apply/matrixP; case.
Qed.

Lemma equiv0r n m p (A : 'M[R]_(n,0)) (B : 'M[R]_(m,p)) :
 (n = m)%N -> (0 = p)%N ->  equivalent A B.
Proof.
move=> eq1 eq2; split=> //.
exists 1%:M, 1%:M; split; try exact: unitmx1.
by apply/matrixP=> i; case.
Qed.

Lemma similar_equiv m n (A : 'M_m) (B : 'M_n) : similar A B -> equivalent A B.
Proof.
case; case: m A B; case: n => //; first by move=> A B _ _; apply: equiv0r.
move=> m n A B eq [P HP HAB].
split=> //; exists P, P^-1; split=> //; first by rewrite unitmx_inv.
rewrite {}HAB -mulmxA mulmxV //; move: B.
by rewrite -eq=> B; rewrite !conform_mx_id mulmx1.
Qed.

Lemma equiv_refl m n (A : 'M[R]_(m,n)) : equivalent A A.
Proof.
split=> //; exists 1%:M, 1%:M.
by split; rewrite ?unitmx1 // conform_mx_id mulmx1 mul1mx.
Qed.

Lemma equiv_sym m1 n1 m2 n2 (A : 'M[R]_(m1,n1)) (B : 'M[R]_(m2,n2)) :
  equivalent A B -> equivalent B A.
Proof.
case: m2 A B=> [A B [eq1 eq2 _]|]; first by apply/equiv0l/esym.
case: n2=> [m2 A B [eq1 eq2 _]|]; first by apply/equiv0r/esym.
case: m1=> [m2 n2 A B []|] //.
case: n1=> [m1 m2 n2 A B []|n1 m1 n2 m2 A B [eq1 eq2 [M [N [HM HN HAB]]]]] //.
split; try exact: esym.
move: B HAB; rewrite -eq1 -eq2=> B; rewrite !conform_mx_id=> HAB.
exists M^-1, N^-1; split; rewrite ?unitmx_inv //.
by rewrite -HAB !mulmxA mulVmx // mul1mx -mulmxA mulmxV // mulmx1.
Qed.

Lemma equiv_trans  m1 n1 m2 n2 m3 n3 (B : 'M[R]_(m2,n2))
  (A : 'M[R]_(m1,n1)) (C : 'M[R]_(m3,n3)) :
  equivalent A B -> equivalent B C -> equivalent A C.
Proof.
case=> eqm12 eqn12 [M1 [N1 [HM1 HN1 HAB]]].
case=> eqm23 eqn23 [M2 [N2 [HM2 HN2 HBC]]].
split; [exact: (etrans eqm12) | exact: (etrans eqn12)|].
move: A B M1 N1 M2 N2 HM1 HN1 HM2 HN2 HAB HBC.
rewrite eqm12 eqn12 eqm23 eqn23=> A B M1 N1 M2 N2 HM1 HN1 HM2 HN2.
rewrite !conform_mx_id=> HAB HBC.
exists (M2 *m M1), (N1 *m N2); split; try by rewrite unitmx_mul; apply/andP.
by rewrite -!(mulmxA M2) (mulmxA (_ *m A)) HAB mulmxA.
Qed.

Lemma equiv_ulblockmx m1 n1 m2 n2 m3 n3 (Aul : 'M[R]_(m1,n1))
 (Adr : 'M[R]_(m2,n2)) (Bul : 'M[R]_(m3,n3)) :
  equivalent Aul Bul ->
  equivalent (block_mx Aul 0 0 Adr) (block_mx Bul 0 0 Adr).
Proof.
case=> eqm eqn [M [N [HM HN HAB]]].
split; rewrite ?eqm ?eqn //.
move: Aul M N HM HN HAB; rewrite eqm eqn => Aul M N HM HN.
rewrite !conform_mx_id=> HAB.
exists (block_mx M 0 0 1%:M), (block_mx N 0 0 1%:M).
split; try by rewrite unitmxE det_ublock det1 mulr1 -unitmxE.
by rewrite !mulmx_block !mulmx0 !mul0mx !addr0 !mul0mx !add0r mulmx1 mul1mx HAB.
Qed.

Lemma equiv_drblockmx m1 n1 m2 n2 m3 n3 (Aul : 'M[R]_(m1,n1))
  (Adr : 'M[R]_(m2,n2))   (Bdr : 'M[R]_(m3,n3)) :
   equivalent Adr Bdr ->
   equivalent (block_mx Aul 0 0 Adr) (block_mx Aul 0 0 Bdr).
Proof.
case=> eqm eqn [M [N [HM HN HAB]]].
split; rewrite ?eqm ?eqn //.
move: Adr M N HM HN HAB; rewrite eqm eqn=> Adr M N HM HN.
rewrite !conform_mx_id=> HAB.
exists (block_mx 1%:M 0 0 M), (block_mx 1%:M 0 0 N).
split; try by rewrite unitmxE det_ublock det1 mul1r -unitmxE.
by rewrite !mulmx_block !mulmx0 !mul0mx !addr0 !mul0mx !add0r mulmx1 mul1mx HAB.
Qed.

Lemma equiv_dgblockmx m1 n1 m2 n2 m3 n3 m4 n4
  (Aul : 'M[R]_(m1,n1)) (Adr : 'M[R]_(m2,n2))
  (Bul : 'M[R]_(m3,n3)) (Bdr : 'M[R]_(m4,n4)) :
  equivalent Aul Bul -> equivalent Adr Bdr ->
  equivalent (block_mx Aul 0 0 Adr) (block_mx Bul 0 0 Bdr).
Proof.
move=> HABu HABd; apply: (equiv_trans (B:=(block_mx Bul 0 0 Adr))).
  exact: equiv_ulblockmx.
exact: equiv_drblockmx.
Qed.

Lemma equiv_cast m1 n1 m2 n2 m3 n3 (eqm : m2 = m3) (eqn : n2 = n3)
 (A : 'M[R]_(m1,n1)) (B : 'M[R]_(m2,n2)) :
  equivalent A (castmx (eqm,eqn) B) <-> equivalent A B.
Proof. by split; case: m3 / eqm A; case: n3 / eqn B. Qed.

Lemma equiv_diag_block : forall l1 l2, size l1 = size l2 ->
   forall (F1 F2 : forall n : nat, nat -> 'M_n.+1),
   (forall i, i < size l1->
    equivalent (F1 (nth 0%N l1 i) i) (F2 (nth 0%N l2 i) i)) ->
   equivalent (diag_block_mx l1 F1) (diag_block_mx l2 F2).
Proof.
case=>[|a l1]; case=> //=.
  by move=> *; exact: equiv_refl.
move=> b l2 /eqP; rewrite eqSS=> /eqP Hsl F1 F2 Hl.
have Hab: equivalent (F1 a 0%N) (F2 b 0%N) by exact: (Hl 0%N).
move: l1 l2 Hsl a b F1 F2 Hab Hl.
apply: seq2_ind=> //= x1 x2 l1 l2 IH a b F1 F2 Hab H.
apply: (equiv_dgblockmx Hab).
apply: IH=>[|i]; first exact: (H 1%N).
exact: (H i.+1).
Qed.

End EquivalentDef.


Section Field.

Import GRing.Theory.
Import polydiv.Pdiv.Ring.
Import RPdiv.
Import polydiv.Pdiv.RingMonic.
Import RPdiv.mon.

Variables R : fieldType.
Variable m n : nat.
Local Open Scope ring_scope.

Theorem similar_fundamental (A: 'M[R]_m) (B : 'M[R]_n) :
  similar A B <-> equivalent (char_poly_mx A) (char_poly_mx B).
Proof.
constructor.
  case: n B=> [B [eq _]|n' B]; first by apply/equiv_sym/equiv0l/esym.
  case: m A=> [A [eq _]|m' A]; first exact: equiv0l.
  case=> eq [P HP HPA]; split=> //.
  move: A P HP HPA; rewrite eq=> A P HP; rewrite !conform_mx_id=> HPA.
  pose M := map_mx polyC P.
  pose N := map_mx polyC P^-1.
  have HM: M \in unitmx by rewrite map_unitmx.
  exists M, N; split=> //; first by rewrite map_unitmx unitmx_inv.
  rewrite mulmxBr mulmxBl mul_mx_scalar -scalemxAl /M /N map_mx_inv.
  rewrite (mulmxV HM) scalemx1 -map_mxM HPA -map_mx_inv -map_mxM.
  by rewrite -mulmxA (mulmxV HP) mulmx1.
case:n B=> [B [eq _ _]|n' B]; first by apply/similar_sym/similar0/esym.
case: m A=> [A [eq _ _]|m' A]; first exact: similar0.
case=> eq _ [M [N [HM HN HA]]]; split=> //.
move: A M N HM HN HA; rewrite eq=> A M N HM HN; rewrite conform_mx_id=> HA.
have [phi [phi_bij phiZ phiC phiG]] := mx_poly_ring_isom R n'.
have: phi M * phi (char_poly_mx A) * phi N = phi (char_poly_mx B).
  by rewrite -!rmorphM -mulmxE HA.
rewrite !{1}rmorphB phiZ !phiC map_polyX=> H.
have HphiM: phi M * ('X - A%:P) = ('X - B%:P) * phi N^-1.
  by rewrite -H -!mulrA -rmorphM mulrV // rmorph1 mulr1.
have HphiN: ('X - A%:P) * phi N = phi M^-1 * ('X - B%:P).
  by rewrite -H !mulrA -rmorphM -mulmxE (mulVmx HM) rmorph1 mul1r.
pose M0 := rmodp_l (phi M) ('X - B%:P).
pose N0 := rmodp (phi N) ('X - B%:P).
pose M1 := rdivp_l (phi M) ('X - B%:P).
pose N1 := rdivp (phi N) ('X - B%:P).
pose R1 := M1 * phi M^-1 + phi N^-1 * N1 - M1 * ('X - A%:P) * N1.
have {}H: M0 * ('X - A%:P) * N0 = (1 - ('X - B%:P) * R1) * ('X - B%:P).
  have HM1: ('X - B%:P) * M1 = phi M - M0.
    by rewrite [phi M](rdivp_l_eq (monicXsubC B)) addrK.
  have HN1: N1 * ('X - B%:P) = phi N - N0.
    by rewrite [phi N](rdivp_eq (monicXsubC B)) addrK.
  rewrite /R1 (mulrBr (_ - B%:P)) (mulrDr (_ - B%:P)) !mulrA HM1 mulrBl 2!mulrDl.
  rewrite mulNr -![_ * N1 * _]mulrA HN1 2!mulrBl.
  rewrite ![_ * (phi N - N0)]mulrBr ![(phi M - M0) * _]mulrBl.
  rewrite -[_ * _ * phi N]mulrA -!rmorphM divrr // mulVr // !rmorph1 !mulr1.
  rewrite mul1r [_ * phi N]mulrBl [(_ - _) * N0]mulrBl H [X in _ = _ + X]opprD.
  rewrite [X in _ + (X - _)]opprD [X in _ + ((X - _) - _)]opprD !opprK.
  rewrite !addrA addrN add0r -{1 3}H.
  rewrite !mulrA -[_ * _ * phi M]mulrA -[_ * _ * phi N^-1]mulrA -!rmorphM.
  rewrite divrr // mulVr // !rmorph1 !mulr1 opprB addrA.
  rewrite -{1}[_ + _ - B%:P]addrA subrK (addrC (M0 * _ * _)) addrK.
  by rewrite opprD opprK addrA addrN add0r.
have HM0: size M0 <= 1.
  by rewrite -ltnS -[leqRHS](size_XsubC B) ltn_rmodp_l polyXsubC_eq0.
have HN0: size N0 <= 1.
  by rewrite -ltnS -[leqRHS](size_XsubC B) ltn_rmodp polyXsubC_eq0.
case: (eqVneq R1 0) => HR1; last first.
  have: size ((1 - ('X - B%:P) * R1) * ('X - B%:P)) <= 2.
    rewrite -H; apply:(leq_trans (size_mul_leq _ _)).
    rewrite (size1_polyC HN0) size_polyC -subn1 leq_subLR addnC.
    apply/(leq_add (leq_b1 _))/(leq_trans (size_mul_leq _ _)).
    by rewrite (size1_polyC HM0) size_polyC size_XsubC addnC; exact:leq_b1.
  have Hsize: size (1 - ('X - B%:P) * R1) = (size R1).+1.
    rewrite addrC size_addl size_opp (size_monicM (monicXsubC B) HR1).
      by rewrite {1}size_XsubC.
    rewrite size_polyC oner_neq0 size_XsubC.
    by move:(size_poly_eq0 R1); case:(size R1)=> //; rewrite (negbTE HR1).
  rewrite size_Mmonic.
  + by rewrite Hsize size_XsubC addnC !ltnS leqn0 size_poly_eq0 (negbTE HR1).
  + by rewrite -size_poly_eq0 Hsize.
  exact: monicXsubC.
move:H; rewrite HR1 mulr0 subr0 mul1r (size1_polyC HM0).
rewrite (size1_polyC HN0)=> /polyP H; move:(H 1%N); move:(H 0%N).
rewrite !coefMC !coefCM !coefD !coefN !coefC !coefX !eqxx !sub0r subr0 mulr1.
rewrite mulrN mulNr; move/eqP; rewrite eqr_opp=> /eqP HM0N0 HM0N0I.
case:(mulmx1_unit HM0N0I)=> HM00 HN00.
exists (M0`_0) => //; rewrite conform_mx_id -HM0N0 mulmxE -(divr1 N0`_0).
by rewrite -[1]HM0N0I invrM // mulrA divrr // mul1r -!mulrA mulVr // mulr1.
Qed.

Lemma similar_mxminpoly m' n' (A : 'M[R]_m'.+1) (B : 'M[R]_n'.+1) :
   similar A B -> mxminpoly A = mxminpoly B.
Proof.
move=> HAB; apply/eqP; rewrite -eqp_monic //; try exact: mxminpoly_monic.
apply/andP; split; apply: mxminpoly_min.
  by apply/(similar_horner (similar_sym HAB))/mx_root_minpoly.
by apply/(similar_horner HAB)/mx_root_minpoly.
Qed.

Lemma similar_char_poly m' n' (A : 'M[R]_m') (B : 'M[R]_n') :
    similar A B -> char_poly A = char_poly B.
Proof.
case=> eq [P HP HAB]; rewrite /char_poly /char_poly_mx.
have H: map_mx polyC P \in unitmx by rewrite map_unitmx.
apply: similar_det; split=> //.
rewrite -eq in B HAB *; rewrite conform_mx_id in HAB.
exists (map_mx polyC P) => //; rewrite conform_mx_id.
by rewrite mulmxDr mulmxDl scalar_mxC mulmxN mulNmx -!map_mxM HAB.
Qed.

End Field.

Section DvdRing.

Local Open Scope ring_scope.
Import GRing.Theory.
Variable R : dvdRingType.

Lemma eqd_equiv n m n' m' (s1 s2 : seq R) : n = n' -> m = m' ->
   size s1 = size s2 -> (forall i, nth 0 s1 i %= nth 0 s2 i) ->
   equivalent (diag_mx_seq n m s1) (diag_mx_seq n' m' s2).
Proof.
move=> <- <-.
case: n=> [_ _|n]; first exact: equiv0l.
case: m=> [_ _|m Hs]; first exact: equiv0r.
move: Hs n m.
pose P := (fun (s1 s2 : seq R) => forall n m,
  (forall i, nth 0 s1 i %= nth 0 s2 i) ->
  equivalent (diag_mx_seq n.+1 m.+1 s1) (diag_mx_seq n.+1 m.+1 s2)).
apply: (seq2_ind (P:=P))=> /= [n m _ | x1 x2 s0 s3 IH n m Hi].
  by rewrite !diag_mx_seq_nil; apply: equiv_refl.
rewrite /P !diag_mx_seq_cons.
have IHi: (forall i : nat, s0`_i %= s3`_i).
  by move=> i; move: (Hi i.+1); rewrite -nth_behead.
have Hxp : x1 %= x2 by move: (Hi 0%N); rewrite nth0.
have Hx12: (@equivalent _ 1 1 1 1 x1%:M x2%:M).
  split=> //; case/eqdP: Hxp=> c Hc Hcx.
  rewrite conform_mx_id.
  exists c%:M; exists 1%:M; split.
  + by rewrite -scalemx1 unitmxZ // unitmx1.
  + by rewrite unitmx1.
  by rewrite mul_scalar_mx scale_scalar_mx mulmx1 Hcx.
apply: (equiv_dgblockmx Hx12).
case: n=> [|n]; first exact: equiv0l.
case: m=> [|m]; first exact: equiv0r.
exact: (IH n m IHi).
Qed.

End DvdRing.
