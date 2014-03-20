(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
(*
    This proof is from:

    Linear Algebra and its Applications

    Volume 184, 15 April 1993, Pages 79–82

    A bijective proof of Muir's identity and the Cauchy-Binet formula

    Jiang Zeng

    Département de Mathématiques Université Louis-Pasteur 7, rue René
    Descartes 67000 Strasbourg Cedex, France

    Received 30 March 1992. Available online 25 March 2002.
    Submitted by Richard A. Brualdi.
*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice finfun.
Require Import matrix  bigop zmodp mxalgebra fingroup.
Require Import minor.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Open Scope ring_scope.

Section BinetCauchy.
Variable R : comRingType.
Variable k l : nat.

Let Z := ({ffun 'I_k -> 'I_l} * ('S_k))%type.

Variable A : 'M[R]_(k,l).
Variable B : 'M[R]_(l,k).

Definition weight (f: {ffun 'I_k -> 'I_l}) (s : 'S_k) :=
  ((-1) ^+ s) * \prod_(i : 'I_k) (A i (f i) * B (f i) (s i)).

Lemma split_sumZ_sf (P : Z -> R) (C : pred {ffun 'I_k -> 'I_l}):
  \sum_(fz : Z | C fz.1) (P fz) =
  \sum_(s: 'S_k) (\sum_(f: {ffun 'I_k -> 'I_l} | C f) (P (f,s))).
Proof.
rewrite exchange_big pair_big /=.
apply/eq_big; first by case => [f s]; rewrite andbT.
by case.
Qed.

Lemma split_sumZ_fs (P : Z -> R) (C : pred {ffun 'I_k -> 'I_l}):
  \sum_(fz : Z | C fz.1) (P fz) =
  \sum_(f: {ffun 'I_k -> 'I_l} | C f) (\sum_(s: 'S_k) (P (f,s))).
Proof.
rewrite pair_big /=.
apply/eq_big ; first by case => [f s]; rewrite andbT.
by case.
Qed.

Lemma detAB_weight : \det (A *m B) = \sum_(fz : Z) (weight fz.1 fz.2).
Proof.
rewrite /determinant /weight.
rewrite (split_sumZ_sf _ xpredT) /=.
apply/eq_big => // s _.
rewrite -big_distrr /=; congr (_ * _).
set F := fun  n m => A n m * B m (s n).
rewrite -(bigA_distr_bigA F) /=.
apply/eq_big => // i _.
by rewrite !mxE.
Qed.

Definition tilt (i j: 'I_k) (z: 'S_k) := (tperm i j * z)%g.

Lemma tiltK (i j: 'I_k) : involutive (tilt i j).
Proof. by move => s; apply/permP => x; rewrite !permM tpermK. Qed.

Lemma tilt_bij (i j: 'I_k) : bijective (tilt i j).
Proof. by apply inv_bij; apply tiltK. Qed.

Lemma tilt_inj (i j : 'I_k) : injective (tilt i j).
Proof. by apply bij_inj; apply tilt_bij. Qed.

Lemma sign_tilt2 (z: 'S_k) (i j: 'I_k) : i != j ->
  (-1)^+(tilt i j z) = -1* ((-1) ^+ z) :>R.
Proof.
move => hij.
rewrite odd_mul_tperm hij /= mulNr mul1r.
by case: (odd_perm z); rewrite /= expr0 expr1 ?opprK.
Qed.

Lemma sig_tilt (z: 'S_k) (i j: 'I_k) : i != j ->
  ~~ odd_perm (tilt i j z) = odd_perm z.
Proof. by move => hij; rewrite odd_mul_tperm hij negbK /=. Qed.

Lemma reindex_with_tilt (P: 'S_k -> R) (i j: 'I_k) : i != j ->
 \sum_(z : 'S_k) (P z) =
 \sum_(z: 'S_k | odd_perm z) (P z + P (tilt i j z)).
Proof.
move => hij.
rewrite (bigID (fun z:'S_k => odd_perm z)) big_split /=; congr (_ + _).
set C := fun z => ~~ (odd_perm z).
set D := fun z => odd_perm z.
set D' := fun z => C (tilt i j z).
have hD : D =1 D' by move=> p; rewrite /D /D' /C sig_tilt.
by rewrite (eq_bigl _ _ hD) /D' -(reindex_inj (@tilt_inj i j)).
Qed.

Lemma fz_tilt_0 (i j: 'I_k) (f: {ffun 'I_k -> 'I_l}) z:
  i != j -> f i = f j ->  weight f z + weight f (tilt i j z) = 0.
Proof.
rewrite /weight => hij hf.
rewrite sign_tilt2 // !mulNr mul1r -mulrBr.
set b1 := \big[*%R/1]_( _ < _ ) _.
set b2 := \big[*%R/1]_( _ < _ ) _.
suff -> : b1 = b2 by rewrite subrr mulr0.
rewrite /b1 {b1} /b2 {b2} (bigD1 j) //= (bigD1 i) //=.
rewrite [RHS](bigD1 j) //= [X in _ = _ * X](bigD1 i) //=.
rewrite !permM tpermR tpermL hf !mulrA.
congr (_ * _).
  by rewrite -!mulrA; congr (_ * _); rewrite mulrC -mulrA mulrCA.
by apply/eq_big => // x /andP [h1 h2]; rewrite permM tpermD // eq_sym.
Qed.

Lemma sum_bad : \sum_(fz : Z | ~~ injectiveb fz.1) (weight fz.1 fz.2) = 0.
Proof.
rewrite (split_sumZ_fs _ (fun x => ~~ injectiveb x)).
apply/big1 => f /injectivePn [x [y hxy hf]] /=.
rewrite (reindex_with_tilt _ hxy).
by apply/big1 => s _; rewrite fz_tilt_0.
Qed.

Definition strictf (p q: nat) (f: 'I_p -> 'I_q) :=
  [forall x : 'I_p, [forall y : 'I_p, (x < y) == (f x < f y)]].

Lemma inj_strictf (p q : nat) (f: 'I_p -> 'I_q) : strictf f -> injective f.
Proof.
move/forallP=> /= hf x y heq.
move/forallP: (hf x) => /= hfx.
move/forallP: (hf y) => /= hfy.
case: (ltngtP x y)=> [||h]; last by apply/ord_inj.
  by rewrite (eqP (hfx y)) heq ltnn.
by rewrite (eqP (hfy x)) heq ltnn.
Qed.

Lemma inj_strictf_ffun (p q : nat) (f: {ffun 'I_p -> 'I_q}) :
 strictf f -> injective f.
Proof. by move=> h; apply: inj_strictf. Qed.

Remark trans_ltn : ssrbool.transitive ltn.
Proof. by move => x y z; apply (@ltn_trans x y z).  Qed.

Lemma sorted_enum  n (P : pred 'I_n): sorted ltn (map val (enum P)).
Proof.
apply (@subseq_sorted _ ltn trans_ltn _ (map val (enum 'I_n))).
- by apply: map_subseq; rewrite {1}/enum_mem enumT filter_subseq.
by rewrite val_enum_ord iota_ltn_sorted.
Qed.

Lemma path_drop : forall (s: seq nat) (i j d x : nat), path ltn x s ->
  i < j -> path ltn (nth d (x :: s) i) (drop i.+1 (x :: s)).
Proof.
elim => [ | hd tl hi] //= [ | i] j d x /andP [hx hp] hij /=.
- by apply/andP.
by apply: (hi _ j.-1 _ hd) => //; move: hij; case: j.
Qed.

Lemma path_ordered_nth (i j d d' x : nat) (s: seq nat): path ltn x s ->
  i < j -> i < size (x::s) -> j < size (x::s) ->
  nth d (x::s) i < nth d' (x::s) j.
Proof.
move => hp hij h1 h2.
have hin : nth d' (x :: s) j \in (drop i.+1 (x :: s)).
- clear hp => /=.
  elim : s x d' i j hij h1 h2 => [ | hd tl hi] x d' [ | i] [ | j] hij //=.
  + rewrite -[j.+1]add1n -[(size tl).+1]add1n ltn_add2l => _ h.
    by rewrite mem_nth.
  rewrite -[i.+1]add1n -[(size tl).+1]add1n -[j.+1]add1n !ltn_add2l =>
    h1 h2.
  by apply: hi.
move/(order_path_min trans_ltn)/allP: (path_drop d hp hij)=> h.
by apply: (h _ hin).
Qed.

Lemma sorted_ordered_nth i j d d' (s: seq nat): sorted ltn s ->
  i < j -> i < size s -> j < size s -> nth d s i < nth d' s j.
Proof.
case: s => [ | hd tl] //= /path_ordered_nth => h h1 h2 h3.
by apply: h.
Qed.

Lemma nth_change_default: forall (s: seq nat) d d' n, n < size s ->
  nth d s n = nth d' s n.
Proof.
elim => [ | hd tl hi] d d' [ | n] //=.
rewrite -[n.+1]add1n -[(size tl).+1]add1n ltn_add2l => h.
by apply: hi.
Qed.

Lemma sorted_ordered_nth_gen (i j d d' x : nat) (s: seq nat):
  sorted ltn s ->
  i < size s -> j < size s -> nth d s i < nth d' s j -> i < j.
Proof.
move => h hi hj hltn.
case: (ltngtP i j) => //.
- move => hji.
  have hgtn := (sorted_ordered_nth d d' h hji hj hi).
  rewrite -(ltnn (nth d s i)).
  apply (ltn_trans hltn).
  by rewrite (nth_change_default d' d hj) (nth_change_default d d' hi).
move => heq.
by move: hltn; rewrite heq (nth_change_default d' d hj) ltnn.
Qed.

Lemma tool_nth : forall (s: seq 'I_l) (n:nat) (x: 'I_n) (d: 'I_l),
 nth (val d) (map val s) x = val (nth d s x).
Proof.
elim => [ | hd tl hi] //= n x d.
- by rewrite !nth_nil.
case: n x => [ | n ]; first by case.
rewrite [n.+1]/(1 + n)%nat => x.
case: (splitP x) => [ j | j hj].
- rewrite [j]ord1 => hx.
  by have -> /= : x = 0 by apply/ord_inj.
have -> /= : x = lift 0 j by apply/ord_inj.
by apply: hi.
Qed.

Lemma cast0 (f: {ffun 'I_k -> 'I_l}) : size (enum (codom f)) = #|codom f|.
Proof. by rewrite cardE. Qed.

Lemma cast1 (f: {ffun 'I_k -> 'I_l}) : injective f -> k = #|codom f|.
Proof.
move => hf.
by rewrite (card_codom hf)  cardT /= size_enum_ord.
Qed.

Lemma step_weight (g f: {ffun 'I_k -> 'I_l}) (pi: 'S_k) (hf : injective f)
  (phi : 'S_k) : (forall x, f x = g (phi x)) ->
  let: sigma :=  (phi^-1 * pi)%g in
    weight f pi = ((-1)^+ phi * \prod_i (A i (g (phi i)))) *
                  ((-1)^+ sigma * \prod_i (B (g i) (sigma i))).
Proof.
move => heq.
rewrite mulrAC mulrA -signr_addb -odd_permM mulgA mulgV mul1g -mulrA.
rewrite /weight big_split /=.
congr (_ * _); rewrite mulrC.
congr (_ * _); last first.
- apply/eq_big => // i _.
  by rewrite heq.
have hinf : injective phi by apply: perm_inj.
rewrite [X in _ = X](reindex_inj  hinf) /=.
apply/eq_big => // i _.
by rewrite -permM mulgA mulgV mul1g heq.
Qed.

(* need the trunk this codom has changed since 1.3 (maybe backward
   compatible, but I couldn't try *)

Definition same_codomb m n (f g: {ffun 'I_m -> 'I_n}) : bool :=
  [forall x, (x \in codom f) == (x \in codom g)].
Definition same_codom m n (f g: {ffun 'I_m -> 'I_n}) :=
  forall x, (x \in codom f) = (x \in codom g).

Lemma same_codomP m n (f g : {ffun 'I_m -> 'I_n}) :
  reflect (same_codom f g) (same_codomb f g).
Proof.
apply: (iffP forallP) => [ h x | h x].
- by rewrite (eqP (h x)).
by rewrite (h x).
Qed.

Definition good (g: {ffun 'I_k -> 'I_l}) : pred {ffun 'I_k -> 'I_l} :=
 fun f => injectiveb f && (same_codomb f g).

Lemma goodP (g f: {ffun 'I_k -> 'I_l}) :
  reflect (injective f /\ same_codom f g) (good g f).
Proof.
apply: (iffP idP).
- case/andP => /injectiveP h1 /forallP h2.
  split => // x.
  by rewrite (eqP (h2 x)).
case => h1 h2.
apply/andP.
split; first by apply/injectiveP.
by apply/forallP => x; rewrite (h2 x).
Qed.

Lemma mem_same_codom (f g: {ffun 'I_k -> 'I_l}) :
  same_codom f g -> forall x,   (f x) \in codom g.
Proof.
move => h x.
by rewrite -h codom_f.
Qed.

(* g^-1 (f x) *)
Definition inv_g_of_fx (g f: {ffun 'I_k -> 'I_l}) :=
  match (same_codomP f g) with
    | ReflectT b => finfun (fun x => iinv (mem_same_codom b x))
    | ReflectF _ => finfun id
  end.

Lemma inv_g_of_fxE (g f: {ffun 'I_k -> 'I_l}) :
  same_codom f g ->
  forall x, g (inv_g_of_fx g f x) = f x.
Proof.
rewrite /inv_g_of_fx => heq.
- case: same_codomP => h x.
  by rewrite !ffunE f_iinv.
by case: h.
Qed.

Lemma inv_g_of_fx_inj (g f: {ffun 'I_k -> 'I_l}): injective f ->
  same_codom f g -> injectiveb (inv_g_of_fx g f).
Proof.
move => hf hc.
apply/injectiveP =>  x y heq.
apply hf.
by rewrite -!(inv_g_of_fxE hc) heq.
Qed.

(* forall g f, if g and f have the same image and f is injective,
   there is a permutation p such that g = f p.

   we build this p from g and f
*)
Definition perm_f (g f: {ffun 'I_k -> 'I_l}) :=
  match goodP g f with
    | ReflectT b => Perm (inv_g_of_fx_inj (proj1 b) (proj2 b))
    | ReflectF _ => 1%g
  end.

Lemma perm_fE  (g f: {ffun 'I_k -> 'I_l}) : injective f ->
  same_codom f g -> forall x, f x = g ((perm_f g f) x).
Proof.
move => hf hc /= x.
rewrite /perm_f PermDef.fun_of_permE /=.
case: goodP => h.
- by rewrite inv_g_of_fxE.
by case: h.
Qed.

Lemma codom_perm (g: {ffun 'I_k -> 'I_l}) (p: 'S_k) :
  forall x, (x \in codom (finfun (g \o p))) = (x \in codom g).
Proof.
move => x.
apply/imageP/imageP.
 - case => /= y h1; rewrite ffunE => h2.
   by exists (p y).
case => y h1 h2.
exists (p^-1 y)%g => //=.
by rewrite ffunE /= permKV.
Qed.

Lemma from_good_to_perm (g: {ffun 'I_k -> 'I_l})
  (P : {ffun 'I_k -> 'I_l} -> R) :  injective  g ->
  \sum_(f | good g f) P f = \sum_(phi : 'S_k) (P (finfun (g \o phi))).
Proof.
move => hg.
rewrite (reindex_onto (fun p:'S_k => finfun (g \o p)) (perm_f g)) /=.
- apply/eq_big => // p.
  have hinj : injective (finfun (g \o p)).
  + have htemp : injective (g \o p)
      by apply: inj_comp => //; apply: perm_inj.
    move => x y; rewrite !ffunE => heq.
    by apply htemp.
  have hcodom : forall x,
    (x \in codom (finfun (g \o p))) = (x \in codom g)
    by move => x; rewrite codom_perm.
  apply/andP; split.
  + apply/andP; split.
    by apply/injectiveP.
  + apply/forallP => x; by rewrite hcodom.
  apply/eqP/permP => x.
  have := (perm_fE hinj hcodom x).
  rewrite ffunE.
  by move/hg ->.
move => /= f.
case/goodP => h1 h2.
apply/ffunP => /= x.
rewrite ffunE.
by rewrite (perm_fE h1 h2).
Qed.

Lemma one_step (g : {ffun 'I_k -> 'I_l}) : injective g ->
  minor id g A * minor g id B =
  \sum_(fz : Z | good g fz.1) weight fz.1 fz.2.
Proof.
move => hg.
rewrite split_sumZ_fs from_good_to_perm //=.
pose sigma (phi pi: 'S_k) : 'S_k := (phi^-1 * pi)%g.
transitivity (\sum_(phi: 'S_k) \sum_(pi : 'S_k)
  (
    ((-1)^+ phi * \prod_i (A i (g (phi i)))) *
    ((-1)^+ (sigma phi pi) * \prod_i (B (g i) (sigma phi pi i)))
  )
); last first.
- apply/eq_big => // phi _.
  apply/eq_big => // pi _.
  have hinj : injective (finfun (g \o phi)).
  + have htemp : injective (g \o phi)
      by apply: inj_comp => //; apply: perm_inj.
    move => x y; rewrite !ffunE => heq.
    by apply htemp.
  rewrite (@step_weight g (finfun (g \o phi)) pi hinj phi) //.
  by move => x; rewrite ffunE.
transitivity( \sum_(phi: 'S_k)
         ((-1) ^+ phi * \big[*%R/1]_i A i (g (phi i)) * (
      \big[+%R/0]_pi
          ((-1) ^+ sigma phi pi * \big[*%R/1]_i B (g i) ((sigma phi pi) i))))); 
  last first.
- apply/eq_big => // phi _.
  by rewrite -big_distrr /=.
rewrite big_distrl /=.
apply/eq_big => // phi _.
congr ( _ * _).
- by congr (_ * _); apply/eq_big => // i _; rewrite mxE.
have inj_s : injective (sigma phi).
- rewrite /sigma => p1 p2 /permP heq.
  apply/permP => x.
  move: (heq (phi x)).
  by rewrite !permE /= /invg /= permK.
rewrite /minor /determinant.
rewrite (reindex_inj inj_s) /=.
apply/eq_big => // pi _.
congr (_ * _).
apply/eq_big => // i _.
by rewrite !mxE.
Qed.

Lemma gather_by_strictness :
  \sum_(g : {ffun 'I_k -> 'I_l} | strictf g)
     \sum_(fz : Z | good g fz.1) weight fz.1 fz.2 =
  \sum_(g : {ffun 'I_k -> 'I_l} | strictf g)
     (minor id g A) * (minor g id B).
Proof.
apply/eq_big => // g hg.
rewrite one_step //.
by apply/inj_strictf.
Qed.

(* from any injective function f, builds a strictly increasing function
   g with the same image ( == enum_val)
*)
Definition strict_from (f: {ffun 'I_k -> 'I_l}) (hf: injective f) :=
  finfun (fun x => @enum_val _ (mem (codom f)) (cast_ord (cast1 hf) x)).

Lemma strict_fromP (f: {ffun 'I_k -> 'I_l})  (hf: injective f):
  strictf (strict_from hf)  /\ same_codom f (strict_from hf).
Proof.
split.
- apply/forallP => x.
  apply/forallP => y.
  have hsorted : sorted ltn (map val (enum (codom f)))
    by apply: sorted_enum.
  apply/eqP.
  rewrite !ffunE /enum_val -!tool_nth.
  apply/idP/idP => [ hxy | ].
  + apply sorted_ordered_nth => //.
    * by rewrite size_map cast0 ltn_ord.
    by rewrite size_map cast0 ltn_ord.
  apply sorted_ordered_nth_gen => //.
  + by rewrite size_map cast0 -(cast1 hf) ltn_ord.
  by rewrite size_map cast0 -(cast1 hf) ltn_ord.
have h1 : enum (codom f) =i codom f by move => y; rewrite mem_enum.
move => y.
apply/imageP/imageP.
- case => x hx hy.
  have hy' : (y \in (enum (codom f)))
    by rewrite h1 hy codom_f.
  have hi : index y (enum (codom f)) < #|codom f|
    by rewrite -cast0 index_mem.
  have hi' : index y (enum (codom f)) < k
    by move: hi; rewrite -cast1.
  exists (Ordinal hi') => //.
  by rewrite !ffunE /enum_val /= nth_index.
case => /= x hx.
rewrite !ffunE => hy.
have : (y \in codom f) by rewrite hy; apply/enum_valP.
case/imageP => x' _ hx'.
by exists x'.
Qed.

Lemma strictf_lift m n (f: {ffun 'I_m.+1 -> 'I_n}) :
  strictf f -> strictf (finfun (fun x => f (lift 0 x))).
Proof.
move/forallP => hf.
apply/forallP => /= x.
apply/forallP => /= y.
rewrite !ffunE.
move/forallP : (hf (lift 0 x)) => hf'.
by rewrite -(eqP (hf' (lift 0 y))).
Qed.

(* such a function is unique :
   two stricly increasing function with the same image are pointwise
   equal
*)
Lemma strictf_uniq : forall m n (f g: {ffun 'I_m -> 'I_n}),
  strictf f -> strictf g -> same_codom f g -> f = g.
Proof.
clear A B Z R k l.
elim => [ | m hi] n f g hf hg hsame; apply/ffunP.
- by case.
move/forallP : (hf) => hf1.
move/forallP : (hg) => hg1.
rewrite [m.+1]/(1 + m)%nat => x.
case: (ltngtP (f 0) (g 0)) => h.
- have h1 : f 0 \in codom g by rewrite -hsame codom_f.
  have [x' heq] : { x' | f 0 = g x'} by exists (iinv h1); rewrite f_iinv.
  move: h; rewrite heq.
  move/forallP : (hg1 x') => hg'.
  by rewrite -(eqP (hg' 0)) ltn0.
- have h1 : g 0 \in codom f by rewrite hsame codom_f.
  have [x' heq] : { x' | g 0 = f x'} by exists (iinv h1); rewrite f_iinv.
  move: h; rewrite heq.
  move/forallP : (hf1 x') => hf'.
  by rewrite -(eqP (hf' 0)) ltn0.
case: (splitP x) => y.
- rewrite [y]ord1 => hy.
  have -> : x = 0 by apply/ord_inj.
  by apply/ord_inj.
move => hy.
have -> : x = lift 0 y by apply/ord_inj.
set f' := finfun (fun x => f (lift 0 x)).
set g' := finfun (fun x => g (lift 0 x)).
have hsame' : forall x, (x \in codom f') = (x \in codom g').
- move => z.
  apply/imageP/imageP.
  + case => /= a _; rewrite ffunE => hz.
    have : z \in codom g by rewrite -hsame hz codom_f.
    case/imageP; rewrite [m.+1]/(1 + m)%nat => x' _.
    case: (splitP x') => j.
    * rewrite [j]ord1 => hx'.
      have -> : x' = 0 by apply/ord_inj.
      move => h'.
      have : f (lift 0 a) = f 0
        by apply/ord_inj; rewrite -hz h h'.
      by move/(inj_strictf hf).
    move => hx'.
    have -> : x' = lift 0 j by apply/ord_inj.
    move => hz'.
    by exists j => //; rewrite ffunE.
  case => /= a _; rewrite ffunE => hz.
    have : z \in codom f by rewrite hsame hz codom_f.
    case/imageP; rewrite [m.+1]/(1 + m)%nat => x' _.
    case: (splitP x') => j.
    * rewrite [j]ord1 => hx'.
      have -> : x' = 0 by apply/ord_inj.
      move => h'.
      have : g (lift 0 a) = g 0
        by apply/ord_inj; rewrite -hz -h h'.
      by move/(inj_strictf hg).
    move => hx'.
    have -> : x' = lift 0 j by apply/ord_inj.
    move => hz'.
    by exists j => //; rewrite ffunE.
move/ffunP : (hi n f' g' (strictf_lift hf) (strictf_lift hg) hsame')
  => heq.
by move: (heq y); rewrite !ffunE => ->.
Qed.

Definition strict_from_f (fz :Z) :=
  match injectiveP fz.1 with
    | ReflectT h => strict_from h
    | ReflectF _ => fz.1
  end.

Lemma strict_from_fP (fz : Z) : injective fz.1 ->
  strictf (strict_from_f fz)  /\ same_codom fz.1 (strict_from_f fz).
Proof.
move => hf.
rewrite /strict_from_f.
case: injectiveP => hinj; first by apply strict_fromP.
by case: hinj.
Qed.

Lemma BinetCauchy:
  \det (A *m B) = \sum_(f : {ffun 'I_k -> 'I_l} | strictf f)
                       (minor id f A * minor f id B).
Proof.
pose cond := fun fz : Z => injectiveb fz.1.
pose ffstrictf := fun (f: {ffun 'I_k -> 'I_l}) => strictf f.
rewrite detAB_weight (bigID cond) /= sum_bad addr0.
rewrite -gather_by_strictness (partition_big strict_from_f ffstrictf) /=.
- apply/eq_big => // g hg.
  apply/congr_big => //.
  case => f pi; rewrite /cond /good /=.
  apply/andP/andP; case => /injectiveP h1.
  + rewrite /strict_from_f.
    case: injectiveP; last by case.
    move => /= hinj.
    move/eqP => heq; split => //.
    case: (strict_fromP hinj) => hlt hrt.
    apply/forallP => x.
    by rewrite -heq (hrt x).
  move/forallP => hsame.
  have hcodom : forall x, (x \in codom f) = (x \in codom g)
    by move => x; rewrite (eqP (hsame x)).
  split; first by apply/injectiveP.
  case: (@strict_from_fP (f,pi) h1) => hstrict hcodom2.
  rewrite (strictf_uniq hstrict hg) // => x.
  by rewrite -hcodom2 hcodom.
move => fz /injectiveP hf.
by case: (strict_from_fP hf).
Qed.

End BinetCauchy.
