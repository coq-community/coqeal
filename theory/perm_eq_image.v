From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section seq_eqType.

Variable T1 : eqType.

Lemma sorted_trans (leT1 leT2 : rel T1) s :
  {in s &, (forall x y, leT1 x y -> leT2 x y)} ->
  sorted leT1 s -> sorted leT2 s.
Proof.
elim: s=> // a [] //= b l IHl leT12 /andP [leT1ab pleT1].
rewrite leT12 ?inE ?eqxx ?orbT // IHl // => x y xbcl ybcl leT1xy.
  by rewrite leT12 // mem_behead.
Qed.


End seq_eqType.

Section FinType.

Lemma enum_ord_enum n : enum 'I_n = ord_enum n.
Proof. by rewrite enumT unlock. Qed.

End FinType.


Section Finfun.

Variables (aT : finType) (rT : eqType).
Variables (f g : aT -> rT).
Variable (P : pred aT).
Hypothesis (Hf : injective f) (Hg : injective g).

Lemma uniq_image (h : aT -> rT):
  injective h -> uniq (image h P).
Proof. by move/map_inj_uniq=> ->; rewrite enum_uniq. Qed.

Lemma perm_eq_image :  {subset (image f P) <= (image g P)} ->
  perm_eq (image f P) (image g P).
Proof.
move=> imfsubimg.
rewrite uniq_perm // ?uniq_image //.
have []:= (uniq_min_size (uniq_image Hf) imfsubimg)=> //.
by rewrite !size_map.
Qed.

End Finfun.

Section BigOp.

Variables (T : Type) (idx : T) (op : Monoid.com_law idx).

Lemma sumn_big s : sumn s = (\sum_(i <- s) i)%N.
Proof.
elim: s=> /= [|a l ->]; first by rewrite big_nil.
by rewrite big_cons.
Qed.
(***Not in bigop.v and I not found a short way to prove this. ****)
Lemma big_lift_ord n F j :
  \big[op/idx]_( i < n.+1 | j != i ) F i = \big[op/idx]_i F (lift j i).
Proof.
case: (pickP 'I_n) => [k0 _ | n0]; last first.
  by rewrite !big1 // => [k /unlift_some[i] | i _]; have:= n0 i.
rewrite (reindex (lift j)).
  by apply: eq_bigl=> k; rewrite neq_lift.
exists (fun k => odflt k0 (unlift j k)) => k; first by rewrite liftK.
by case/unlift_some=> k' -> ->.
Qed.

Variable R : idomainType.
Open Scope ring_scope.

Lemma lead_coef_prod (s : seq {poly R}) :
  \prod_(p <- s) lead_coef p = lead_coef (\prod_(p <- s) p).
Proof.
elim: s=> [|a l IHl]; first by rewrite !big_nil lead_coef1.
by rewrite !big_cons lead_coefM -IHl.
Qed.

Import GRing.Theory.

Lemma monic_leadVMp (p : {poly R}) : (lead_coef p) \is a GRing.unit ->
  ((lead_coef p)^-1 *: p) \is monic.
Proof. by move=> *; apply/monicP; rewrite lead_coefZ mulVr. Qed.

End BigOp.

Section Matrix.
Import GRing.Theory.
Local Open Scope ring_scope.


Section matrix_Type.

Variable T : Type.
(**** This lemma is useful to rewrite in a big expression, and it is unsightly
to do a "have" in a proof for proving that. *********)
Lemma matrix_comp k l m n (E : 'I_k -> 'I_l -> T) (F : 'I_n -> 'I_k) G :
  \matrix_(i < n, j < m) ((\matrix_(i0 < k, j0 < l) E i0 j0) (F i) (G j)) =
  \matrix_(i, j) (E (F i) (G j)).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End matrix_Type.

Section matrix_fieldType.

Variable F : fieldType.

(* mx_poly *)
Lemma horner_mx_dvdp n (p q : {poly F}) (A : 'M_n.+1) :
  (dvdp p q) -> horner_mx A p = 0 -> horner_mx A q = 0.
Proof. by case/dvdpP=> r ->; rewrite rmorphM=> /= ->; rewrite mulr0. Qed.

Lemma mxminpolyP n (A : 'M[F]_n.+1) (p : {poly F}) :
  p \is monic -> horner_mx A p = 0 ->
  (forall q, horner_mx A q = 0 -> (dvdp p q)) ->
  p = mxminpoly A.
Proof.
move=> pmon eqpA0 pdvq.
apply/eqP; rewrite -eqp_monic //; last exact: mxminpoly_monic.
apply/andP; split.
  by apply/pdvq/mx_root_minpoly.
exact: mxminpoly_min.
Qed.

End matrix_fieldType.

Section matrix_ringType.
Variable R : ringType.


Lemma char_block_mx m n (A : 'M[R]_m) (D : 'M[R]_n) B C :
  char_poly_mx (block_mx A B C D) =
 block_mx (char_poly_mx A) (map_mx polyC (-B))
          (map_mx polyC (-C)) (char_poly_mx D).
Proof.
apply/matrixP=> i j; rewrite !mxE.
case: splitP=> k eqik; rewrite !mxE; case: splitP=> l eqjmpl; rewrite !mxE;
rewrite -!(inj_eq (@ord_inj _)) eqik eqjmpl ?eqn_add2l // rmorphN.
  by rewrite ltn_eqF ?ltn_addr // sub0r.
by rewrite gtn_eqF ?ltn_addr // sub0r.
Qed.

Lemma char_dblock_mx m n (A : 'M[R]_m) (B : 'M[R]_n) :
  char_poly_mx (block_mx A 0 0 B) =
  block_mx (char_poly_mx A) 0 0 (char_poly_mx B).
Proof. by rewrite char_block_mx !oppr0 !map_mx0. Qed.

End matrix_ringType.

End Matrix.

Section poly_idomainType.

Variable R : idomainType.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma coprimep_irreducible (p q : {poly R}) : ~~(p %= q) ->
  irreducible_poly p -> irreducible_poly q -> coprimep p q.
Proof.
move=> neqdpq [szpgt1 Heqdp] [szqgt1 Heqdq].
have gcdvp:= (dvdp_gcdl p q).
have gcdvq:= (dvdp_gcdr p q).
rewrite /coprimep; apply: contraT => neqsz1.
move: (Heqdp _ neqsz1 gcdvp); rewrite eqp_sym /eqp dvdp_gcd.
case/andP=> [/andP [ _ pdvq]] _.
move: (Heqdq _ neqsz1 gcdvq); rewrite eqp_sym /eqp dvdp_gcd.
case/andP=> [/andP [qdvp _]] _.
by rewrite /eqp pdvq qdvp in neqdpq.
Qed.

Lemma irreducible_dvdp_seq (p r : {poly R}) s :
    irreducible_poly p -> p \is monic -> (dvdp p r) ->
    (forall q, q \in s -> irreducible_poly q) ->
    (forall q, q \in s -> q \is monic) ->
    r = \prod_(t <- s) t ->
    p \in s.
Proof.
move=> pIrr pm.
elim: s r => [r pdvr _ _|a l IHl r pdvr Irr mon].
  rewrite big_nil=> eqr1; move: pdvr pIrr.
  rewrite eqr1 dvdp1 /irreducible_poly=> /eqP ->.
  by rewrite ltnn; case.
rewrite big_cons=> eqrM; move: pdvr; rewrite eqrM=> pdvM.
case/boolP: (eqp p a)=>[|neqdpa].
  have am: a \is monic by apply: mon; rewrite mem_head.
  by rewrite eqp_monic // => /eqP ->; rewrite mem_head.
have Hia: irreducible_poly a by apply: Irr; rewrite mem_head.
have cppa := coprimep_irreducible neqdpa pIrr Hia.
rewrite (Gauss_dvdpr _ cppa) in pdvM.
apply/mem_behead/(IHl _ pdvM)=> // q qinl.
  by apply: Irr; rewrite mem_behead.
by rewrite mon // mem_behead.
Qed.

Lemma unicity_decomposition (s1 s2 : seq {poly R}) : forall (p : {poly R}),
  (forall r, r \in s1 -> irreducible_poly r) ->
  (forall r, r \in s2 -> irreducible_poly r) ->
  (forall r, r \in s1 -> r \is monic) ->
  (forall r, r \in s2 -> r \is monic) ->
  p = \prod_(r <- s1) r ->  p = \prod_(r <- s2) r ->
  perm_eq s1 s2.
Proof.
elim: s1 s2=> [|a1 l1 IHl s2 p Irr1 Irr2 mon1 mon2].
  case=> // a l p _ Irr2 _ mon2->.
  rewrite big_nil big_cons=> eq1M.
  have: irreducible_poly a by apply: Irr2; rewrite mem_head.
  rewrite /irreducible_poly; case.
  by rewrite ltnNge leq_eqVlt -dvdp1 eq1M dvdp_mulr.
rewrite big_cons=> eqpM eqpbig /=.
have a1ins2: a1 \in s2.
  apply: (irreducible_dvdp_seq _ _ _ Irr2 mon2 eqpbig).
  +by apply: Irr1; rewrite mem_head.
  -by rewrite mon1 // mem_head.
  by rewrite eqpM dvdp_mulr.
rewrite perm_sym (perm_trans (perm_to_rem a1ins2)) //.
rewrite perm_cons perm_sym.
have nza1: a1 != 0.
  by apply: irredp_neq0; apply: Irr1; rewrite mem_head.
rewrite (perm_big _ (perm_to_rem a1ins2)) /= big_cons eqpM in eqpbig.
have/(mulfI nza1) eqbig := eqpbig.
set q:= \prod_(j <- l1) j.
apply: (IHl _ q)=> // r Hr.
  +by apply: Irr1; rewrite mem_behead.
  -by apply: Irr2; rewrite (mem_rem Hr).
  +by rewrite mon1 // mem_behead.
  -by rewrite mon2 // (mem_rem Hr).
Qed.

End poly_idomainType.
