(** Authors: Erik Martin-Dorel and Pierre Roux, 2016-2017 *)
Require Import ZArith NArith FMaps FMapAVL.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice finfun tuple fintype ssralg bigop.
From CoqEAL Require Import hrel.
From CoqEAL Require Import refinements.
From CoqEAL Require Import param binord binnat.
From CoqEAL Require Import seqmx (* for zipwith and eq_seq *).
From CoqEAL Require Import ssrcomplements.
(* Multivariate polynomials from
   https://github.com/math-comp/multinomials.git
   Tested with 5b46e50983ee68dd1b6932e7e4a3bfc1113e7360 *)
From SsrMultinomials Require Import mpoly freeg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * CoqEAL refinement for effective multivariate polynomials built on FMaps *)

(** N.B.: Do not use {vm_,native_}compute directly on the various
    [..._eff] functions as FMaps contain proof terms about balancing of binary
    trees. Rather surround the polynomial expression with a call to
    list_of_mpoly_eff. *)

Import Refinements.Op.

Local Open Scope ring_scope.

(** BEGIN FIXME this is redundant with PR CoqEAL/CoqEAL#3 *)
Arguments refines A%type B%type R%rel _ _. (* Fix a scope issue with refines *)

Hint Resolve list_R_nil_R.
(** END FIXME this is redundant with PR CoqEAL/CoqEAL#3 *)

(** Tip to leverage a Boolean condition *)
Definition sumb (b : bool) : {b = true} + {b = false} :=
  if b is true then left erefl else right erefl.

Definition Rord0 {n1} : 'I_n1 -> nat -> Type := fun x y => x = y :> nat.

Lemma Rord0_eq (n1 : nat) i i' :
  refines (@Rord0 n1) i i' -> i = i' :> nat.
Proof. by rewrite refinesE =>->. Qed.

(** ** Part 1: Generic operations *)

Section effmpoly_generic.

(** Monomials *)

(** [mnmd i d] represents the monomial X_i^d *)
Definition mnmd {n} (i : 'I_n) (d : nat) :=
  [multinom (if (i == j :> nat) then d else 0%N) | j < n].

Definition mpvar {T : ringType} {n} (c : T) d i : {mpoly T[n]} :=
  c *: 'X_[mnmd i d].

Definition seqmultinom := seq binnat.N.

Definition mnm0_seq {n} : seqmultinom := nseq n 0%num.

Definition mnmd_seq {n} (i : nat) (d : binnat.N) : seqmultinom :=
  nseq i 0%num ++ [:: d] ++ nseq (n - i - 1) 0%num.

(** Multiplication of multinomials *)
Definition mnm_add_seq (m1 m2 : seqmultinom) := map2 +%C m1 m2.

Definition mdeg_eff : seqmultinom -> binnat.N := foldl +%C 0%C.

Fixpoint mnmc_lt_seq_aux (s1 s2 : seq binnat.N) {struct s1} : bool :=
  match s1, s2 with
    | [::], [::] => false
    | [::], _ => true
    | x1 :: s1', [::] => false
    | x1 :: s1', x2 :: s2' =>
      (x1 < x2)%C || (x1 == x2)%C && mnmc_lt_seq_aux s1' s2'
  end.
Definition mnmc_lt_seq (s1 s2 : seq binnat.N) : bool :=
  mnmc_lt_seq_aux (mdeg_eff s1 :: s1) (mdeg_eff s2 :: s2).

Definition mnmc_eq_seq := eq_seq (fun n m : binnat.N => n == m)%C.

Lemma mnmc_eq_seqP s1 s2 : reflect (mnmc_eq_seq s1 s2) (s1 == s2).
Proof.
move: s2; elim s1 => {s1}[|a1 s1 Hind] s2.
{ now case s2 => [|n l]; apply (iffP idP). }
case s2 => {s2}[|a2 s2]; [by apply (iffP idP)|].
specialize (Hind s2); rewrite /mnmc_eq_seq /=; apply (iffP idP).
{ move/eqP => [Hs Ha]; rewrite Hs Rnat_eqxx /=.
  exact/Hind/eqP. }
by move/andP => [Ha Hs]; apply/eqP; f_equal; apply /eqP => //; apply/Hind.
Qed.

End effmpoly_generic.

Module MultinomOrd <: OrderedType.
Definition t := seqmultinom.
Definition eq : t -> t -> Prop := mnmc_eq_seq.
Definition lt : t -> t -> Prop := mnmc_lt_seq.

Lemma intro_eq x y :
  (mnmc_lt_seq x y = false) -> (mnmc_lt_seq y x = false) -> mnmc_eq_seq x y.
Proof.
rewrite /mnmc_lt_seq /=.
rewrite !Rnat_ltE !Rnat_eqE.
case Hlt : (_ < _)=>//=; case Hlt' : (_ < _)=>//=; move: Hlt Hlt'.
rewrite !ltnNge !negb_false_iff !eqn_leq =>->->/=.
elim: x y => [|hx tx Hind]; case=> // hy ty.
rewrite /= !Rnat_ltE !Rnat_eqE.
case (ltnP (spec_N hx) (spec_N hy)) => //= Hxy;
  case (ltnP (spec_N hy) (spec_N hx)) => //= Hyx.
have Exy : (spec_N hx == spec_N hy).
by apply/eqP/anti_leq; rewrite Hyx.
rewrite /mnmc_eq_seq /= Rnat_eqE Exy; rewrite eq_sym in Exy; rewrite Exy /=.
exact: Hind.
Qed.

(** Remark: only compare is used in implementation (eq_dec isn't). *)
Definition compare (x y : t) : Compare lt eq x y :=
  match sumb (mnmc_lt_seq x y) with
  | left prf => LT prf
  | right prf =>
    match sumb (mnmc_lt_seq y x) with
    | left prf' => GT prf'
    | right prf' => EQ (intro_eq prf prf')
    end
  end.

Lemma eq_dec (x y : t) : {eq x y} + {~ eq x y}.
Proof. by rewrite /eq; case (mnmc_eq_seq x y); [left|right]. Qed.

Lemma eq_refl : forall x : t, eq x x.
Proof. by move=> x; apply/mnmc_eq_seqP/eqP. Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. move=> x y /mnmc_eq_seqP/eqP =>->; apply eq_refl. Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. by move=> x y z /mnmc_eq_seqP/eqP =>->. Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
move=> x y z; rewrite /lt /mnmc_lt_seq.
set x' := _ :: x; set y' := _ :: y; set z' := _ :: z.
clearbody x' y' z'; clear x y z; move: x' y' z'.
elim => [|hx tx Hind] y z; [by case y => // hy ty; case z|].
case y => // hy ty; case z => // hz tz.
move/orP; rewrite !Rnat_E => -[Hxy|Hxy].
{ move/orP; rewrite !Rnat_E => -[Hyz|Hyz];
  apply/orP; rewrite !Rnat_E; left; [by move: Hyz; apply ltn_trans|].
  move/andP in Hyz; destruct Hyz as [Hyz Hyz'].
  by move/eqP in Hyz; rewrite -Hyz. }
move/andP in Hxy; destruct Hxy as [Hxy Hxy']; move/eqP in Hxy.
rewrite /mnmc_lt_seq_aux !Rnat_E Hxy.
move/orP => [Hyz|Hyz]; apply/orP; [by left|right].
move/andP in Hyz; destruct Hyz as [Hyz Hyz']; rewrite Hyz /=.
by move: Hyz'; apply Hind.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
move=> x y; rewrite /lt /mnmc_lt_seq /=; move/orP; elim.
{ move=> Hlt Heq; move: Heq Hlt; move/mnmc_eq_seqP/eqP->.
  by rewrite Rnat_E ltnn. }
move/andP; case=>_.
move=> Hlt /mnmc_eq_seqP/eqP Heq; move: Hlt; rewrite Heq.
elim y => [//|h t Hind] /orP [H|H]; [by move: H; rewrite Rnat_E ltnn|].
move/andP in H; apply Hind, H.
Qed.

End MultinomOrd.

(** Generic implementation of multivariate polynomials that can be instanciated
with e.g. [M := FMapList.Make MultinomOrd] or [M := FMapAVL.Make MultinomOrd] *)

Module FMapMultipoly (M : Sfun MultinomOrd).

Arguments M.empty {elt}.

Definition effmpoly := M.t.

Module E := MultinomOrd.
Module P := WProperties_fun E M.
Module F := P.F.

Section MoreProps.

Definition singleton T key (val : T) := M.add key val M.empty.

Lemma singleton_mapsto {T} k k' (e e' : T) :
  M.MapsTo k e (singleton k' e') -> (k = k' /\ e = e').
Proof.
rewrite F.add_mapsto_iff; elim; move=> [Hk He]; [split; [|by[]]|].
by move/mnmc_eq_seqP/eqP in Hk.
by move: He; rewrite F.empty_mapsto_iff.
Qed.

Lemma singleton_in_iff {T} y k (e : T) :
  M.In y (singleton k e) <-> E.eq k y.
Proof.
split; [move/F.add_in_iff|move=> H; apply/F.add_in_iff].
by intuition; move/F.empty_in_iff in H.
by left.
Qed.

(* Variants of stdlib lemmas in Type *)
Lemma add_mapsto_iff_dec {T} (m : M.t T) (x y : M.key) (e e' : T) :
  (M.MapsTo y e' (M.add x e m) <=>
  {(E.eq x y) * (e = e')} + {(~ E.eq x y) * (M.MapsTo y e' m)})%type.
Proof.
split.
destruct (E.eq_dec x y); [left|right].
split; auto.
symmetry; apply (F.MapsTo_fun (e':=e) H).
exact: M.add_1.
split; auto; apply M.add_3 with x e; auto.
case; case => H1 H2.
- rewrite H2; exact: M.add_1.
- exact: M.add_2.
Qed.

Lemma MIn_sig T (k : M.key) (m : M.t T) : M.In k m -> {e | M.MapsTo k e m}.
Proof.
move=> HIn.
case Ee : (M.find k m) => [e|].
  by exists e; apply: M.find_2.
by move/F.in_find_iff in HIn.
Qed.

Lemma map_mapsto_iff_dec {T T'} (m : M.t T) (x : M.key) (b : T') (f : T -> T') :
  M.MapsTo x b (M.map f m) <=> {a : T | b = f a /\ M.MapsTo x a m}.
Proof.
split.
case_eq (M.find x m) => [e He|] H.
exists e.
split.
apply (F.MapsTo_fun (m:=M.map f m) (x:=x)); auto.
apply M.find_2.
by rewrite F.map_o /option_map He.
by apply M.find_2.
move=> H0.
have H1 : (M.In x (M.map f m)) by exists b; auto.
have [a H2] := MIn_sig (M.map_2 H1).
rewrite (M.find_1 H2) in H; discriminate.
intros (a,(H,H0)).
subst b.
exact: M.map_1.
Qed.

(** As in the latest version of CoqEAL, all relations are in [Type],
while most lemmas from FMaps are in [Prop], we will sometimes need to
"lift" these lemmas in [Type] by using decidability arguments. *)

Lemma or_dec P Q : decidable P -> decidable Q -> P \/ Q -> {P} + {Q}.
Proof.
case; first by move=> *; left.
move=> nP [|nQ]; first by move=> *; right.
move=> K; exfalso; by destruct K.
Qed.

Lemma MIn_dec {T} k (m : M.t T) : decidable (M.In k m).
Proof.
case E: (M.mem k m); [left|right]; apply/F.mem_in_iff =>//.
by rewrite E.
Qed.

Lemma map2_2_dec {T T' T''} (m : M.t T) (m' : M.t T') (x : M.key)
  (f : option T -> option T' -> option T'') :
  M.In x (M.map2 f m m') -> {M.In x m} + {M.In x m'}.
Proof.
move=> HIn; apply: or_dec; try exact: MIn_dec.
exact: M.map2_2 HIn.
Qed.

Lemma map2_ifft {T T' T''} (m : M.t T) (m' : M.t T') (x : M.key)
  (f : option T -> option T' -> option T'') :
  (forall t t', f (Some t) t' <> None) ->
  (forall t t', f t (Some t') <> None) ->
  M.In x (M.map2 f m m') <=> {M.In x m} + {M.In x m'}.
Proof.
move=> H1 H2.
split; first exact: map2_2_dec.
case=> HIn; apply F.in_find_iff;
  erewrite M.map2_1; try solve [by left|by right];
  move/F.in_find_iff in HIn;
  by case: M.find HIn.
Qed.

Lemma HdRel_dec T (R : T -> T -> Prop) a l :
  (forall a b, decidable (R a b)) -> decidable (HdRel R a l).
Proof.
move=> Hdec.
elim: l => [//|b l [IHl|IHl]]; first by left.
- have [Rab|Rab] := Hdec a b.
  + by left; constructor.
  + by right=> K; inversion K.
- have [Rab|Rab] := Hdec a b.
  + by left; constructor.
  + by right=> K; inversion K.
Qed.

Lemma Sorted_dec T (R : T -> T -> Prop) l :
  (forall a b, decidable (R a b)) -> decidable (Sorted R l).
Proof.
move=> Hdec.
elim: l =>[//| a l [IHl|IHl]]; first by left.
have [Ral|Ral] := @HdRel_dec T R a l Hdec.
- left; constructor =>//.
- by right => K; apply: Ral; inversion K.
- by right => K; apply: IHl; inversion K.
Qed.

Inductive HdRelT (A : Type) (R : A -> A -> Prop) (a : A) : seq A -> Type :=
    HdRelT_nil : HdRelT R a [::]
  | HdRelT_cons : forall (b : A) (l : seq A), R a b -> HdRelT R a (b :: l).

Inductive SortedT (A : Type) (R : A -> A -> Prop) : seq A -> Type :=
    SortedT_nil : SortedT R [::]
  | SortedT_cons : forall (a : A) (l : seq A), SortedT R l -> HdRelT R a l -> SortedT R (a :: l).


Lemma HdRelT_dec T (R : T -> T -> Prop) a l :
  (forall a b, decidable (R a b)) -> HdRel R a l -> HdRelT R a l.
Proof.
move=> Hdec H0.
elim: l H0 => [//|b l] H0; first by left.
have [Rab|Rab] := Hdec a b.
+ by move=> ?; constructor.
+ by move=> K0; exfalso; inversion K0.
Qed.

Lemma SortedT_dec T (R : T -> T -> Prop) l :
  (forall a b, decidable (R a b)) -> Sorted R l -> SortedT R l.
Proof.
move=> Hdec H0.
elim: l H0 =>[//| a l] H0; first by left.
have [Ral|Ral] := @HdRel_dec T R a l Hdec.
- move=> SRal; constructor.
  + by apply H0; inversion SRal.
  + exact: HdRelT_dec.
- move => K; constructor.
  + by apply: H0; inversion K.
  + by exfalso; apply: Ral; inversion K.
Qed.

End MoreProps.

Definition list_of_mpoly {R : ringType} {n} (p : {mpoly R[n]}) :
  seq ('X_{1..n} * R) := [seq (m, p@_m) | m <- path.sort mnmc_le (msupp p)].

Section effmpoly_generic_2.

Context {T : Type} `{!zero_of T, !one_of T}.
Context `{!add_of T, !opp_of T, !sub_of T, !mul_of T, !eq_of T}.
Context {n : nat}.

Definition list_of_mpoly_eff (p : effmpoly T) : seq (seqmultinom * T) :=
  [seq mc <- M.elements p | negb (mc.2 == 0)%C].

Definition mpoly_of_list_eff (l : seq (seqmultinom * T)) : effmpoly T :=
  foldl (fun m mc => M.add mc.1 mc.2 m) M.empty l.

Definition mp0_eff : effmpoly T := M.empty.

Definition mp1_eff  := singleton (@mnm0_seq n) (1%C : T).

Definition mpvar_eff (c : T) (d : binnat.N) (i : nat) : effmpoly T :=
  singleton (@mnmd_seq n i d) c.

Definition mpolyC_eff (c : T) : effmpoly T :=
  singleton (@mnm0_seq n) c.

Definition mpolyX_eff (m : seqmultinom) : effmpoly T :=
  singleton m 1%C.

Definition mpoly_scale_eff (c : T) (p : effmpoly T) : effmpoly T :=
  M.map (fun x => c * x)%C p.

Definition mpoly_add_eff : effmpoly T -> effmpoly T -> effmpoly T :=
  M.map2 (fun c1 c2 =>
    match c1, c2 with
    | Some c1, Some c2 => Some (c1 + c2)%C
    | Some c, _ | _, Some c => Some c
    | None, None => None
    end).

Definition mpoly_sub_eff : effmpoly T -> effmpoly T -> effmpoly T :=
  M.map2 (fun c1 c2 =>
    match c1, c2 with
    | Some c1, Some c2 => Some (c1 - c2)%C
    | Some c, _ => Some c
    | _, Some c => Some (- c)%C
    | None, None => None
    end).

Definition mult_monomial_eff (m : seqmultinom) (c : T) (p : effmpoly T) : effmpoly T :=
  M.fold (fun m' c' (*acc*) => M.add (mnm_add_seq m m') (c * c')%C (*acc*)) p M.empty.

Definition mpoly_mul_eff (p q : effmpoly T) : effmpoly T :=
  M.fold (fun m c => mpoly_add_eff (mult_monomial_eff m c q)) p mp0_eff.

Definition mpoly_exp_eff (p : effmpoly T) (n : binnat.N) := N.iter n (mpoly_mul_eff p) mp1_eff.

Definition comp_monomial_eff (m : seqmultinom) (c : T) (lq : seq (effmpoly T)) : effmpoly T :=
  let mq := zipwith mpoly_exp_eff lq m in
  mpoly_scale_eff c (foldr mpoly_mul_eff mp1_eff mq).

Definition comp_mpoly_eff (lq : seq (effmpoly T)) (p : effmpoly T) : effmpoly T :=
  M.fold (fun m c => mpoly_add_eff (comp_monomial_eff m c lq)) p mp0_eff.

End effmpoly_generic_2.

Derive Inversion inv_InA with
  (forall (A : Type) (eqA : A -> A -> Prop) (x : A) (s : seq A), @InA A eqA x s) Sort Prop.

(** ** Part 2: Proofs for proof-oriented types and programs *)

Section effmpoly_theory.

(** *** Data refinement for seqmultinom *)

Definition multinom_of_seqmultinom n (m : seqmultinom) : option 'X_{1..n} :=
  let m' := map spec_N m in
  if sumb (size m' == n) is left prf then
    Some (Multinom (@Tuple n nat m' prf))
  else None.

Definition multinom_of_seqmultinom_val n (m : seqmultinom) : 'X_{1..n} :=
  odflt (@mnm0 n) (multinom_of_seqmultinom n m).

Definition seqmultinom_of_multinom n (m : 'X_{1..n}) :=
  let: Multinom m' := m in map implem_N (tval m').

Lemma implem_NK : cancel implem_N spec_N.
Proof.
move=> n; symmetry; apply refinesP.
have{1}->: n = spec_id (implem_id n) by [].
refines_apply.
by rewrite refinesE.
Qed.

Lemma spec_NK : cancel spec_N implem_N.
Proof. by move=> x; rewrite -[RHS](ssrnat.nat_of_binK x). Qed.

Lemma seqmultinom_of_multinomK n :
  pcancel (@seqmultinom_of_multinom n) (@multinom_of_seqmultinom n).
Proof.
move=> x; rewrite /seqmultinom_of_multinom /multinom_of_seqmultinom.
case: sumb => [prf|].
  congr Some; apply: val_inj; simpl; apply: val_inj; simpl; case: (x).
  by move=> t; rewrite -map_comp (eq_map implem_NK) map_id.
case: x => [t].
by rewrite size_tuple eqxx.
Qed.

(** Main refinement predicate for [multinom]s *)
Definition Rseqmultinom {n} := ofun_hrel (@multinom_of_seqmultinom n).

Lemma refine_size
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  `{ref_mm' : !refines Rseqmultinom m m'} :
  size m' = n.
Proof.
move: ref_mm'.
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb =>// prf _.
rewrite size_map in prf.
exact/eqP.
Qed.

Lemma refine_nth_def
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  (i : 'I_n) x0 :
  refines Rseqmultinom m m' -> spec_N (nth x0 m' i) = m i.
Proof.
move=> rMN; move: (rMN).
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb =>// prf [] <-.
rewrite multinomE /= (tnth_nth (spec_N x0)) (nth_map x0) //.
by move: prf; rewrite size_map; move/eqP ->.
Qed.

Lemma refine_nth
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom)
  (i : 'I_n) :
  refines Rseqmultinom m m' -> spec_N (nth 0%num m' i) = m i.
Proof. exact: refine_nth_def. Qed.

Lemma refine_seqmultinomP
  (n : nat) (m : 'X_{1..n}) (m' : seqmultinom) :
  size m' = n ->
  (forall i : 'I_n, spec_N (nth 0%num m' i) = m i) ->
  refines Rseqmultinom m m'.
Proof.
move=> eq_sz eq_nth.
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom /ofun_hrel.
case: sumb => [prf|].
  congr Some; apply: val_inj; simpl.
  apply: eq_from_tnth => i.
  rewrite (tnth_nth 0%N) /= (nth_map 0%num) ?eq_nth //.
  by move: prf; rewrite size_map; move/eqP ->.
by rewrite size_map eq_sz eqxx.
Qed.

Lemma refine_seqmultinom_of_multinom (n : nat) (m : 'X_{1..n}) :
  refines Rseqmultinom m (seqmultinom_of_multinom m).
Proof.
by rewrite refinesE /Rseqmultinom /ofun_hrel seqmultinom_of_multinomK.
Qed.

Lemma refine_multinom_of_seqmultinom_val (n : nat) (m : seqmultinom) :
  size m == n ->
  refines Rseqmultinom (multinom_of_seqmultinom_val n m) m.
Proof.
move=> Hsz.
rewrite refinesE /Rseqmultinom /multinom_of_seqmultinom_val /ofun_hrel.
case_eq (multinom_of_seqmultinom n m) => //.
rewrite /multinom_of_seqmultinom; case sumb => //.
by rewrite size_map Hsz.
Qed.

Lemma refine_mnm0 n : refines Rseqmultinom (@mnm0 n) (@mnm0_seq n).
Proof.
apply refine_seqmultinomP.
  by rewrite size_nseq.
move=> i; rewrite nth_nseq if_same multinomE (tnth_nth 0%N) nth_map //=.
by rewrite size_enum_ord.
Qed.

Lemma refine_mnmd {n1} :
  refines (Rord0 ==> Rnat ==> Rseqmultinom) (@mnmd n1) (@mnmd_seq n1).
Proof.
(* First, ensure that n1 > 0, else 'I_n1 would be empty *)
case: n1 => [|n1]; first by rewrite refinesE => -[].
eapply refines_abstr => i i' ref_i.
eapply refines_abstr => j j' ref_j.
apply: refine_seqmultinomP.
  rewrite /mnmd_seq !(size_cat,size_nseq) /= -subnDA addnA addn1 subnKC //.
  by move: ref_i; rewrite refinesE /Rord0; move<-.
move=> k.
rewrite /mnmd_seq /mnmd multinomE (tnth_nth 0%N) /=.
rewrite !(nth_cat,nth_nseq).
rewrite (nth_map ord0); last by rewrite size_enum_ord.
case: ifP.
  rewrite if_same size_nseq nth_enum_ord //.
  move=> Hic; rewrite ifF //.
  apply/negP; move/eqP => Keq.
  move/Rord0_eq in ref_i.
  by rewrite -ref_i -Keq ltnn in Hic.
move/negbT; rewrite size_nseq -ltnNge ltnS => Hi.
rewrite nth_enum_ord //.
case: ifP.
  move/eqP <-; move/Rord0_eq: ref_i <-.
  rewrite subnn /=.
  have->: j = spec_id j by [].
  symmetry; eapply refinesP; refines_apply.
move/negbT/eqP => Hneq.
move/Rord0_eq in ref_i; rewrite -ref_i in Hi *.
case: (ltnP i k) => Hci.
  by rewrite -(@prednK (k - i)) ?subn_gt0 //= nth_nseq if_same.
by exfalso; apply/Hneq/anti_leq; rewrite Hi.
Qed.

Global Instance refine_mnm_add n :
  refines (Rseqmultinom ==> Rseqmultinom ==> Rseqmultinom)
  (@mnm_add n) mnm_add_seq.
Proof.
apply refines_abstr => mnm1 mnm1' ref_mnm1.
apply refines_abstr => mnm2 mnm2' ref_mnm2.
apply/refine_seqmultinomP.
{ rewrite /mnm_add_seq size_map2.
  by rewrite (@refine_size _ mnm1) (@refine_size _ mnm2) minnn. }
move=> i.
rewrite /mnm_add_seq (nth_map2 _ (da := 0%num) (db := 0%num)) //; last first.
  by rewrite (@refine_size _ mnm1) (@refine_size _ mnm2).
rewrite mnmDE -!refine_nth.
exact: nat_of_add_bin.
Qed.

Global Instance refine_mdeg n :
  refines (Rseqmultinom ==> eq) (@mdeg n) mdeg_eff.
Proof.
rewrite refinesE.
elim n => [|n' Hn'] m m' rm; apply trivial_refines in rm.
{ by rewrite mdegE big_ord0 (size0nil (@refine_size _ _ _ rm)). }
move: rm; case m'=> [|h t] rm; [by apply (@refine_size _ _ _) in rm|].
rewrite mdegE big_ord_recl /mdeg_eff /=.
rewrite -(refine_nth _ rm) /spec_N /=.
set s := bigop _ _ _; set p := add_op; set z := zero_op.
suff ->: s = foldl p z t; rewrite {}/p {}/z.
{ set z := zero_op; generalize z.
  elim: t {rm z} h => [|h' t' IH] h z /=.
  { by rewrite /add_op /add_N N.add_comm nat_of_add_bin. }
  rewrite IH /add_op /add_N -!N.add_assoc; do 3 f_equal.
  by rewrite N.add_comm. }
pose mt := [multinom m (fintype.lift ord0 i) | i < n'].
suff ->: s = mdeg mt.
{ apply Hn', refinesP, refine_seqmultinomP.
  { suff: size (h :: t) = n'.+1; [by rewrite /= => H; injection H|].
    by apply (@refine_size _ m _). }
  by move=> i; rewrite multinomE tnth_mktuple -(refine_nth _ rm). }
rewrite /s mdegE /mt; apply eq_bigr=> i _.
by rewrite multinomE tnth_mktuple.
Qed.

Lemma multinom_of_seqmultinom_inj n x y :
  size x = n -> size y = n ->
  multinom_of_seqmultinom n x = multinom_of_seqmultinom n y -> x = y.
Proof.
move=> Sx Sy; rewrite /multinom_of_seqmultinom.
case (sumb _) => [prfx|] /=; [|by rewrite size_map Sx eqxx].
case (sumb _) => [prfy|] /=; [|by rewrite size_map Sy eqxx].
case; exact: map_spec_N_inj.
Qed.

Lemma multinom_of_seqmultinom_val_inj n x y :
  size x = n -> size y = n ->
  multinom_of_seqmultinom_val n x = multinom_of_seqmultinom_val n y -> x = y.
Proof.
move=> Sx Sy; rewrite /multinom_of_seqmultinom_val /multinom_of_seqmultinom.
case (sumb _) => [prfx|] /=; [|by rewrite size_map Sx eqxx].
case (sumb _) => [prfy|] /=; [|by rewrite size_map Sy eqxx].
case; exact: map_spec_N_inj.
Qed.

Lemma Rseqmultinom_eq n (x : 'X_{1..n}) x' y y' :
  refines Rseqmultinom x x' ->
  refines Rseqmultinom y y' ->
  (x == y) = (x' == y').
Proof.
move=> Hx Hy; apply/idP/idP => H.
{ have Sx' := @refine_size _ _ _ Hx.
  have Sy' := @refine_size _ _ _ Hy.
  apply/eqP.
  move: H Hy Hx; rewrite refinesE /Rseqmultinom /ofun_hrel; move/eqP=>-><-.
  by apply multinom_of_seqmultinom_inj. }
apply/eqP; move: H Hx Hy.
rewrite refinesE /Rseqmultinom /ofun_hrel; move/eqP=>->->.
by move=> H; inversion H.
Qed.

Global Instance refine_mnmc_lt n :
  refines (Rseqmultinom ==> Rseqmultinom ==> eq)
    (@mnmc_lt n) (mnmc_lt_seq).
Proof.
rewrite refinesE=> m1 m1' rm1 m2 m2' rm2.
apply trivial_refines in rm1; apply trivial_refines in rm2; rewrite /mnmc_lt.
rewrite -ltEmnm.
case: (boolP (m1 == m2)) => /= [E|].
{ suff: mnmc_eq_seq m1' m2'.
  { move=> E'; symmetry.
    move: E => /eqP ->; rewrite order.Order.POrderTheory.ltxx.
    apply negbTE; apply /negP => K.
    by apply (E.lt_not_eq K). }
  by apply /mnmc_eq_seqP; rewrite -(Rseqmultinom_eq rm1 rm2). }
move=> nE.
rewrite /mnmc_lt_seq /order.Order.lt /=.
rewrite mpoly.ltmc_def eq_sym nE /=.
have rmdeg := refine_mdeg n; rewrite refinesE in rmdeg.
rewrite /eq_op /eq_N /lt_op /lt_N.
rewrite /mnmc_le.
rewrite order.Order.SeqLexiOrder.Exports.lexi_cons.
rewrite (rmdeg _ _ (refinesP rm1)) (rmdeg _ _ (refinesP rm2)) => {rmdeg}.
rewrite /order.Order.le /=.
rewrite (_ : order.Order.SeqLexiOrder.le _ _ = mnmc_lt_seq_aux m1' m2').
{ rewrite leq_eqVlt.
  apply/idP/idP.
  { case eqP => /= He.
    { rewrite He leqnn /= => ->.
      apply /orP; right.
      rewrite andbC /=.
      move: He; rewrite -Nat2N.inj_iff !nat_of_binK => ->.
      by rewrite /is_true N.eqb_eq. }
    move=> /andP [Hlt _].
    apply /orP; left.
    by rewrite /is_true N.ltb_lt; apply /Rnat_ltP. }
  move=> /orP [Hlt|/andP [Heaq ->]].
  { apply /andP; split.
    { apply /orP; right.
      by move: Hlt; rewrite /is_true N.ltb_lt => /Rnat_ltP. }
    apply /implyP => Hle.
    exfalso; move: Hlt.
    rewrite /is_true N.ltb_lt => /Rnat_ltP.
    by rewrite /spec_N ltnNge Hle. }
  move: Heaq => /Neqb_ok => ->.
  by apply /andP; split; [rewrite eqxx|apply /implyP]. }
elim: n m1 m1' rm1 m2 m2' rm2 nE => [|n IH] m1 m1' rm1 m2 m2' rm2 nE.
{ move: rm1=> /(@refine_size _) /size0nil ->.
  move: rm2=> /(@refine_size _) /size0nil -> /=.
  apply/negbTE/negP=> H; move: nE => /eqP; apply.
  by case m1, m2; rewrite tuple0; symmetry; rewrite tuple0. }
case: m1' rm1 => [|h1 t1 rm1]; [by move/(@refine_size _)|].
case: m2' rm2 => [|h2 t2 rm2]; [by move/(@refine_size _)|].
move: nE; case: m1 rm1=> m1; case: m1 => m1; case: m1=> [//|h1' t1'] sm1 /= rm1.
case: m2 rm2 => m2; case: m2 => m2; case: m2 => [//|h2' t2'] sm2 /= rm2 => nE.
have st1 : size t1' == n; [by rewrite -eqSS|].
have st2 : size t2' == n; [by rewrite -eqSS|].
have Hh1 : nat_of_bin h1 = h1'.
{ by move: (refine_nth ord0 rm1); rewrite /spec_N => ->. }
have rt1 : refines Rseqmultinom [multinom Tuple st1] t1.
{ apply refine_seqmultinomP.
  { by move: (@refine_size _ _ _ rm1)=> /= /eqP; rewrite eqSS=> /eqP. }
  move=> i; move: (refine_nth (fintype.lift ord0 i) rm1).
  by rewrite /= =>->; rewrite !multinomE !(tnth_nth 0%N) /=. }
have Hh2 : nat_of_bin h2 = h2'.
{ by move: (refine_nth ord0 rm2); rewrite /spec_N => ->. }
have rt2 : refines Rseqmultinom [multinom Tuple st2] t2.
{ apply refine_seqmultinomP.
  { by move: (@refine_size _ _ _ rm2)=> /= /eqP; rewrite eqSS=> /eqP. }
  move=> i; move: (refine_nth (fintype.lift ord0 i) rm2).
  by rewrite /= =>->; rewrite !multinomE !(tnth_nth 0%N) /=. }
rewrite /order.Order.lt /= /eq_op /eq_N /lt_op /lt_N.
move: (@refine_nth _ _ _ ord0 rm1) => /=.
rewrite multinomE /spec_N (tnth_nth 0%N) /= => <-.
move: (@refine_nth _ _ _ ord0 rm2) => /=.
rewrite multinomE /spec_N (tnth_nth 0%N) /= => <-.
rewrite /order.Order.le /=.
apply/idP/idP.
{ rewrite leq_eqVlt.
  move=> /andP [/orP [Heq12|Hlt12] /implyP Himpl].
  { move: Heq12 => /eqP; rewrite -Nat2N.inj_iff !nat_of_binK => Heq12.
    apply /orP; right.
    apply /andP; split.
    { rewrite Heq12; apply N.eqb_refl. }
    rewrite -(IH _ _ rt1 _ _ rt2).
    { by apply Himpl; rewrite Heq12. }
    apply /eqP => Hst12.
    move: nE => /eqP; apply.
    do 2 (apply val_inj => /=).
    apply f_equal2.
    { by rewrite -Hh1 Heq12. }
    by move: Hst12 => []. }
  apply /orP; left.
  by rewrite /is_true N.ltb_lt; apply /Rnat_ltP. }
move=> /orP [Hlt12|/andP [Heq12 Hltseq]];
  (apply /andP; split; [|apply /implyP => Hle21]).
{ apply ltnW.
  by move: Hlt12; rewrite /is_true N.ltb_lt => /Rnat_ltP. }
{ exfalso; move: Hle21.
  apply /negP; rewrite -ltnNge.
  by move: Hlt12; rewrite /is_true N.ltb_lt => /Rnat_ltP. }
{ by move: Heq12 => /Neqb_ok => ->. }
rewrite (IH _ _ rt1 _ _ rt2) => [//|].
apply /negP => /eqP [Ht12'].
move: nE => /negP; apply; apply /eqP.
do 2 (apply val_inj => /=).
apply f_equal2 => [|//].
by rewrite -Hh1 -Hh2; move: Heq12 => /Neqb_ok => ->.
Qed.

Definition mpoly_of_effmpoly (T : ringType) n (p' : effmpoly T) : option (mpoly n T) :=
  if P.for_all (fun k _ => size k == n)%N p' then
    Some [mpoly [freeg [seq (a.2, multinom_of_seqmultinom_val n a.1) |
                        a <- M.elements p']]]
  else None.

Definition mpoly_of_effmpoly_val (T : ringType) n (p' : effmpoly T) : mpoly n T :=
  odflt 0 (mpoly_of_effmpoly n p').

(** Main refinement predicate for multivariate polynomials *)
Definition Reffmpoly `{T : ringType, n : nat} :=
  ofun_hrel (@mpoly_of_effmpoly T n).

Lemma eq_key_elt_eq T x y : (M.eq_key_elt (elt:=T)) x y <-> x = y.
Proof.
split.
{ move=> [H1 H2].
  rewrite (surjective_pairing x) (surjective_pairing y); f_equal=> //.
  by apply/eqP/mnmc_eq_seqP. }
move=> ->; split=> //; apply E.eq_refl.
Qed.

Lemma in_InA_eq_key_elt_iff (T : eqType) x s :
  x \in s <-> InA (M.eq_key_elt (elt:=T)) x s.
Proof.
split.
{ elim s => // h t Hind; rewrite inE; move/orP => [Hh|Ht].
  { by move: Hh => /eqP ->; apply InA_cons_hd; split; [apply E.eq_refl|]. }
  by apply InA_cons_tl, Hind. }
elim s => [|h t Hind]; [by rewrite InA_nil|].
rewrite InA_cons; elim.
{ by move/eq_key_elt_eq=>->; rewrite inE eqxx. }
by move/Hind; rewrite inE orb_comm=>->.
Qed.

Lemma in_fst_InA_eq_key_iff (T : Type) x s :
  x.1 \in [seq x.1 | x <- s] <-> InA (M.eq_key (elt:=T)) x s.
Proof.
split.
{ elim s => // h t Hind; rewrite inE; move/orP => [Hh|Ht].
  { apply InA_cons_hd; change (M.eq_key _ _) with (E.eq x.1 h.1).
    move: Hh => /eqP ->; apply E.eq_refl. }
  by apply InA_cons_tl, Hind. }
elim s => [|h t Hind]; [by rewrite InA_nil|].
rewrite InA_cons; elim.
{ change (M.eq_key _ _) with (E.eq x.1 h.1).
  by move/mnmc_eq_seqP/eqP =>->; rewrite inE eqxx. }
by rewrite inE orb_comm; move/Hind =>->.
Qed.

Lemma NoDupA_eq_key_uniq_fst elt s :
  NoDupA (M.eq_key (elt:=elt)) s -> uniq [seq i.1 | i <- s].
Proof.
elim s => // h t Hind Hnd /=.
inversion Hnd as [x|h' t' H1 H2].
apply/andP; split; [|by apply Hind].
by apply/negP => Hin; apply H1, in_fst_InA_eq_key_iff.
Qed.

Lemma refine_size_mpoly (n : nat) T (p : mpoly n T) (p' : effmpoly T)
  `{ref_pp' : !refines Reffmpoly p p'} :
  forall m, M.In m p' -> size m == n.
Proof.
move: ref_pp'.
rewrite refinesE /Reffmpoly /mpoly_of_effmpoly /ofun_hrel.
set t := P.for_all _ _; case_eq t => //.
rewrite /t (P.for_all_iff _); [|by move=> m _ /mnmc_eq_seqP /eqP <-].
by move=> H _ m [e Hme]; apply (H m e).
Qed.

Lemma refine_find_mpoly (n : nat) T (p : mpoly n T) (p' : effmpoly T) :
  refines Reffmpoly p p' ->
  forall m m', refines Rseqmultinom m m' -> p@_m = odflt 0 (M.find m' p').
Proof.
rewrite !refinesE /Reffmpoly /mpoly_of_effmpoly /ofun_hrel.
set t := P.for_all _ _; case_eq t => //.
rewrite /t (P.for_all_iff _); [|by move=> m _ /mnmc_eq_seqP /eqP <-].
move=> H_sz H; injection H; move=> {H} H m m' Hm'.
rewrite -H mcoeff_MPoly coeff_Freeg.
case_eq (M.find m' p') => [c|] Hc.
{ change c with ((c, m).1); change m with ((c, m).2).
  apply precoeff_mem_uniqE.
  { rewrite /predom -map_comp.
    rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
    rewrite map_comp map_inj_in_uniq.
    { apply NoDupA_eq_key_uniq_fst, M.elements_3w. }
    move=> x y Hx Hy; apply multinom_of_seqmultinom_val_inj.
    { move: Hx; move/mapP => [xe Hxe ->].
      apply/eqP /(H_sz _ xe.2) /M.elements_2.
      by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
    move: Hy; move/mapP => [ye Hye ->].
    apply/eqP /(H_sz _ ye.2) /M.elements_2.
    by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
  apply M.find_2, M.elements_1, in_InA_eq_key_elt_iff in Hc.
  apply/mapP; exists (m', c) => //=; f_equal.
  move: Hm'; rewrite /Rseqmultinom /ofun_hrel /multinom_of_seqmultinom_val.
  by case (multinom_of_seqmultinom n m') => // m'' Hm''; injection Hm''. }
apply precoeff_outdom.
rewrite /predom -map_comp.
rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
apply/negP=> Hm; apply F.not_find_in_iff in Hc; apply Hc.
move/mapP in Hm; destruct Hm as [xe Hxe Hm].
rewrite F.elements_in_iff; exists xe.2.
rewrite -in_InA_eq_key_elt_iff.
suff: m' = xe.1; [by move=> ->; rewrite -surjective_pairing|].
move: Hm' Hm; rewrite /Rseqmultinom /ofun_hrel /multinom_of_seqmultinom_val /=.
rewrite /multinom_of_seqmultinom /seqmultinom_of_multinom.
case (sumb _) => [prf|] //= Hm; injection Hm; move=> <- {Hm}.
case (sumb _) => [prf'|] //=.
  by move=> H'; inversion H'; apply: map_spec_N_inj.
rewrite size_map => Hf _.
rewrite size_map in prf.
rewrite (H_sz xe.1 xe.2) in Hf => //; apply M.elements_2.
by rewrite -in_InA_eq_key_elt_iff -surjective_pairing.
Qed.

Lemma refine_effmpolyP (n : nat) T (p : mpoly n T) (p' : effmpoly T) :
  (forall m, M.In m p' -> size m == n)%N ->
  (forall m m', refines Rseqmultinom m m' -> p@_m = odflt 0 (M.find m' p')) ->
  refines Reffmpoly p p'.
Proof.
move=> eq_sz eq_monom.
assert (Hsz : P.for_all (fun (k : M.key) (_ : T) => size k == n) p').
{ rewrite /is_true (P.for_all_iff _) => k e Hke.
  { by apply eq_sz; exists e. }
  by move=> _ _ _; move: Hke; move/mnmc_eq_seqP/eqP ->. }
rewrite refinesE /Reffmpoly /mpoly_of_effmpoly /ofun_hrel ifT //; f_equal.
apply mpolyP => m.
pose m' := seqmultinom_of_multinom m.
have Hm' : refines Rseqmultinom m m'.
  by rewrite refinesE; apply seqmultinom_of_multinomK.
rewrite (eq_monom _ _ Hm') mcoeff_MPoly coeff_Freeg.
case_eq (M.find m' p') => [c|] Hc.
{ change c with ((c, m).1); change m with ((c, m).2).
  apply precoeff_mem_uniqE.
  { rewrite /predom -map_comp.
    rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
    rewrite map_comp map_inj_in_uniq.
    { apply NoDupA_eq_key_uniq_fst, M.elements_3w. }
    move=> x y Hx Hy; apply multinom_of_seqmultinom_val_inj.
    { move: Hx; move/mapP => [xe Hxe ->].
      apply/eqP /eq_sz; exists xe.2; apply/(M.elements_2 (e:=xe.2)).
      by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
    move: Hy; move/mapP => [ye Hye ->].
    apply/eqP /eq_sz; exists ye.2; apply/(M.elements_2 (e:=ye.2)).
    by apply in_InA_eq_key_elt_iff; rewrite -surjective_pairing. }
  apply M.find_2, M.elements_1, in_InA_eq_key_elt_iff in Hc.
  apply/mapP; exists (m', c) => //=; f_equal.
  by rewrite /m' /multinom_of_seqmultinom_val seqmultinom_of_multinomK. }
apply precoeff_outdom.
rewrite /predom -map_comp.
rewrite (@eq_map _ _ _ ((multinom_of_seqmultinom_val n) \o fst)) //.
apply/negP=> Hm; apply F.not_find_in_iff in Hc; apply Hc.
move/mapP in Hm; destruct Hm as [xe Hxe Hm].
rewrite F.elements_in_iff; exists xe.2.
rewrite -in_InA_eq_key_elt_iff /m' Hm /= /multinom_of_seqmultinom_val.
rewrite /multinom_of_seqmultinom /seqmultinom_of_multinom.
case (sumb _) => [prf|] /=.
rewrite -map_comp (eq_map spec_NK) map_id -surjective_pairing //.
rewrite size_map (@eq_sz xe.1); [by []|exists xe.2].
by apply /M.elements_2 /in_InA_eq_key_elt_iff; rewrite -surjective_pairing.
Qed.

(** *** Data refinement for effmpoly *)

Context {T : ringType}.
Instance : zero_of T := 0.
Instance : one_of T := 1.
Instance : add_of T := +%R.
Instance : opp_of T := -%R.
Global Instance sub_instR : sub_of T := fun x y => (x - y).
Instance mul_instR : mul_of T := *%R.
Instance : eq_of T := fun x y => x == y.

Lemma refine_seq_multinom_coeff n (s : seq ('X_{1..n} * T)) s' :
  all (fun mc => size mc.1 == n) s' ->
  s = [seq (multinom_of_seqmultinom_val n mc.1, mc.2) |mc <- s'] ->
  refines (list_R (prod_R Rseqmultinom eq)) s s'.
Proof.
rewrite refinesE.
elim: s' s=> [|h' t' IH]; case=> [//|h t] //=.
case/andP => Hsh Hst [Hh Ht]; constructor.
{ apply/prod_RI; rewrite Hh; split=>//.
  by apply refinesP; eapply refine_multinom_of_seqmultinom_val. }
by apply IH.
Qed.

Lemma in_InA_iff mc l : mc \in l <-> InA (M.eq_key_elt (elt:=T)) mc l.
Proof.
elim l=> [|h t IH]; [by split=>// H; inversion H|].
rewrite in_cons; split.
{ move=>/orP []; [by move/eqP->; left; rewrite eq_key_elt_eq|].
  by move=> Hmc; right; apply IH. }
move=> H; inversion H as [mc' l' Hmc [Hmc' Hl']|mc' l' Hmc [Hmc' Hl']].
{ by apply/orP; left; apply/eqP; apply eq_key_elt_eq. }
by apply/orP; right; rewrite IH.
Qed.

Lemma uniq_map_filter (T' T'' : eqType) (s : seq T') C (E : T' -> T'') :
  uniq [seq E i | i <- s] -> uniq [seq E i | i <- s & C i].
Proof.
elim s=> [//|h t IH] /= /andP [] Hh Ht.
case (C h)=>/=; [|by apply IH]; apply/andP; split; [|by apply IH].
apply/negP=>H; move/negP in Hh; apply Hh; apply/mapP.
move: H; move/mapP=> [] x Hx Hx'; exists x=>//; move: Hx.
by rewrite mem_filter=>/andP [].
Qed.

Global Instance refine_list_of_mpoly_eff n :
  refines (Reffmpoly ==>  list_R (prod_R Rseqmultinom eq))
    (@list_of_mpoly T n) list_of_mpoly_eff.
Proof.
apply refines_abstr => p p' rp.
rewrite /list_of_mpoly_eff.
have Hs : all (fun mc : seq binnat.N * T => size mc.1 == n)
            [seq mc <- M.elements p' | ~~ (mc.2 == 0)%C].
{ apply/allP=> mc; rewrite mem_filter; move/andP=> [] _ Hmc.
  apply (refine_size_mpoly (ref_pp' := rp)).
  rewrite F.elements_in_iff; exists mc.2.
  by rewrite -in_InA_iff -surjective_pairing. }
apply refine_seq_multinom_coeff=> //; rewrite /list_of_mpoly.
suff : path.sort mnmc_le (msupp p)
  = [seq multinom_of_seqmultinom_val n mc.1 |
     mc <- M.elements p' & ~~ (mc.2 == 0)].
{ set l := path.sort _ _; set l' := filter _ _.
  move=> H; apply (eq_from_nth (x0:=(0%MM, 0))).
  { by rewrite size_map H !size_map. }
  move=> i; rewrite size_map=> Hi.
  have Hi' : i < size l'; [by move: Hi; rewrite H size_map|].
  rewrite (nth_map 0%MM) // H !(nth_map (@mnm0_seq n, 0)) //; f_equal.
  set mc := nth _ _ _.
  erewrite (refine_find_mpoly (p' := p') (m':=mc.1) rp). (* erewrite?! *)
  { rewrite (M.find_1 (e:=mc.2)) // F.elements_mapsto_iff -in_InA_iff.
    rewrite -surjective_pairing.
    suff: mc \in l'; [by rewrite mem_filter=>/andP []|by apply mem_nth]. }
  apply refine_multinom_of_seqmultinom_val; move: Hs; move/allP; apply.
  rewrite -/l' /mc; apply (mem_nth (mnm0_seq, 0) Hi'). }
apply (path.eq_sorted (leT:=mnmc_le)).
{ apply mpoly.lemc_trans. }
{ apply mpoly.lemc_anti. }
{ apply path.sort_sorted, lemc_total. }
{ have Se := M.elements_3 p'.
  pose lef := fun x y : _ * T => mnmc_lt_seq x.1 y.1.
  pose l := [seq mc <- M.elements p' | mc.2 != 0]; rewrite -/l.
  have : path.sorted lef l.
  { apply path.sorted_filter; [by move=> x y z; apply E.lt_trans|].
    clear l; move: Se; set l := _ p'; elim l=> [//|h t IH].
    move=> H; inversion H as [|h' t' Ht Hht [Hh' Ht']]; move {H h' t' Hh' Ht'}.
    rewrite /path.sorted; case_eq t=>[//|h' t'] Ht' /=; apply /andP; split.
    { by rewrite Ht' in Hht; inversion Hht. }
    by rewrite -/(path.sorted _ (h' :: t')) -Ht'; apply IH. }
  case_eq l=> [//|h t Hl] /= /(path.pathP (@mnm0_seq n, 0)) H.
  apply/(path.pathP 0%MM)=> i; rewrite size_map=> Hi.
  rewrite /mnmc_le -leEmnm order.Order.POrderTheory.le_eqVlt; apply/orP; right.
  rewrite (nth_map (@mnm0_seq n, 0)) //; move/allP in Hs.
  move: (H _ Hi); rewrite /lef/is_true=><-; apply refinesP.
  eapply refines_apply; [eapply refines_apply; [by apply refine_mnmc_lt|]|].
  { case: i Hi=> /= [|i'] Hi; [|apply ltnW in Hi].
    { apply refine_multinom_of_seqmultinom_val, Hs.
      by rewrite -/l Hl in_cons eqxx. }
    rewrite (nth_map (@mnm0_seq n, 0)) //.
    apply refine_multinom_of_seqmultinom_val, Hs.
    by rewrite -/l Hl in_cons; apply/orP; right; rewrite mem_nth. }
  apply refine_multinom_of_seqmultinom_val, Hs.
  by rewrite -/l Hl in_cons; apply/orP; right; rewrite mem_nth. }
apply uniq_perm.
{ rewrite path.sort_uniq; apply msupp_uniq. }
{ change (fun _ => multinom_of_seqmultinom_val _ _)
  with ((fun m => multinom_of_seqmultinom_val n m) \o (fst (B:=T))).
  rewrite map_comp map_inj_in_uniq.
  { apply (@uniq_map_filter _ _ (M.elements p')).
    apply NoDupA_eq_key_uniq_fst, M.elements_3w. }
  move=> m m' Hm Hm'; apply multinom_of_seqmultinom_val_inj.
  { by move/allP in Hs; move: Hm=>/mapP [x Hx] ->; apply/eqP /Hs. }
  by move/allP in Hs; move: Hm'=>/mapP [x Hx] ->; apply/eqP /Hs. }
move=> m; rewrite path.mem_sort; apply/idP/idP.
{ pose m' := seqmultinom_of_multinom m.
  rewrite mcoeff_msupp=>Hin; apply/mapP; exists (m', p@_m).
  { rewrite mem_filter /= Hin /= in_InA_iff; apply M.elements_1, M.find_2.
    move: Hin; erewrite (@refine_find_mpoly _ _ _ _ rp _ m').
    { by case (M.find _ _)=>//; rewrite eqxx. }
    apply refine_seqmultinom_of_multinom. }
  by rewrite /= /m' /multinom_of_seqmultinom_val seqmultinom_of_multinomK. }
move/mapP=> [] mc; rewrite mem_filter=>/andP [] Hmc2; rewrite in_InA_iff.
rewrite {1}(surjective_pairing mc) -F.elements_mapsto_iff.
rewrite F.find_mapsto_iff mcoeff_msupp=> Hmc1 ->.
erewrite (@refine_find_mpoly _ _ _ _ rp _ mc.1); [by rewrite Hmc1|].
apply refine_multinom_of_seqmultinom_val; move/allP in Hs; apply Hs.
rewrite mem_filter Hmc2 /= in_InA_iff (surjective_pairing mc).
by rewrite -F.elements_mapsto_iff; apply M.find_2.
Qed.

Global Instance refine_mp0_eff n : refines (@Reffmpoly T n) 0 mp0_eff.
Proof.
apply: refine_effmpolyP.
- by move=> m /F.empty_in_iff Hm.
- by move=> m m' ref_m; rewrite F.empty_o mcoeff0.
Qed.

Global Instance refine_mp1_eff n : refines (@Reffmpoly T n) 1 (mp1_eff (n := n)).
Proof.
apply refine_effmpolyP.
- rewrite /mp1_eff => k /singleton_in_iff/mnmc_eq_seqP/eqP <-.
  by rewrite size_nseq.
- move=> m m' Hm; rewrite mcoeff1 F.add_o.
  have H0 := refine_mnm0 n.
  rewrite (Rseqmultinom_eq Hm H0).
  case: E.eq_dec => [EQ|nEQ].
  + by move/mnmc_eq_seqP/eqP: EQ <-; rewrite eqxx.
  + rewrite eq_sym; move/mnmc_eq_seqP/negbTE: nEQ ->.
    by rewrite F.empty_o.
Qed.

Global Instance refine_mpvar_eff {n1} :
  refines (eq ==> Rnat ==> Rord0 ==> Reffmpoly (T := T) (n := n1))
  mpvar (mpvar_eff (n := n1)).
Proof.
case: n1 => [|n1].
  by rewrite refinesE; move=> p p' Hp q q' Hq [] i' Hi.
apply refines_abstr => c c' ref_c; apply refines_abstr => d d' ref_d.
apply refines_abstr => i i' ref_i.
assert (Hmnmd : refines Rseqmultinom (mnmd i d) (@mnmd_seq n1.+1 i' d')).
{ eapply refines_apply;
  first eapply refines_apply;
  first eapply refine_mnmd; by tc. }
apply refine_effmpolyP.
{ move=> m [e Hme]; move: Hme; rewrite /mpvar_eff.
  move/(@singleton_mapsto T)=> [-> _].
  by apply/eqP; apply (@refine_size _ (mnmd i d)). }
move=> m m' Hm; rewrite mcoeffZ mcoeffX.
rewrite (Rseqmultinom_eq Hmnmd Hm) eq_sym.
case_eq (m' == (@mnmd_seq n1.+1 i' d')).
{ move/eqP => Hm'; rewrite Hm'.
  rewrite F.add_eq_o; last exact: E.eq_refl.
  by rewrite /= GRing.mulr1 (refines_eq ref_c). }
move=> Hm'; rewrite F.add_neq_o /=.
{ by rewrite GRing.mulr0; rewrite F.empty_o. }
by apply/mnmc_eq_seqP; rewrite eq_sym Hm'.
Qed.

Arguments mpolyC {n R} c.
Global Instance refine_mpolyC_eff n :
  refines (eq ==> Reffmpoly (T := T) (n := n))
  mpolyC (mpolyC_eff (n := n)).
Proof.
apply refines_abstr => c c' ref_c.
rewrite !refinesE in ref_c; rewrite -{}ref_c {c'}.
apply refine_effmpolyP.
{ move=> m [e Hme]; move: Hme; rewrite /mpvar_eff.
  by move/(@singleton_mapsto T)=> [-> _]; rewrite size_nseq eqxx. }
move=> m m' Hm; rewrite mcoeffC.
have Hm0 := @refine_mnm0 n.
rewrite (Rseqmultinom_eq Hm Hm0).
case_eq (m' == @mnm0_seq n).
{ move/eqP => Hm'; rewrite Hm'.
  by rewrite F.add_eq_o; [rewrite GRing.mulr1|apply E.eq_refl]. }
move=> Hm'; rewrite F.add_neq_o /=.
{ by rewrite GRing.mulr0; rewrite F.empty_o. }
by apply/mnmc_eq_seqP; move: Hm'; rewrite eq_sym =>->.
Qed.

Arguments mpolyX {n R} m.
Global Instance refine_mpolyX_eff n :
  refines (Rseqmultinom ==> Reffmpoly (T := T) (n := n))
  mpolyX mpolyX_eff.
Proof.
apply refines_abstr => m m' ref_m.
apply refine_effmpolyP.
{ move=> m'' [e Hme]; move: Hme; rewrite /mpolyX_eff.
  move/(@singleton_mapsto T)=> [-> _].
  by apply/eqP; apply (@refine_size _ m). }
move=> m'' m''' Hm; rewrite mcoeffX.
rewrite (Rseqmultinom_eq ref_m Hm) eq_sym.
case_eq (m''' == m').
{ move/eqP => Hm'; rewrite Hm'.
  by rewrite F.add_eq_o /=; [|by apply E.eq_refl]. }
move=> Hm'; rewrite F.add_neq_o //=.
{ by rewrite F.empty_o. }
by apply/mnmc_eq_seqP; rewrite eq_sym Hm'.
Qed.

Lemma MapsTo_mcoeff {n} m m' p p' a :
  refines (Reffmpoly (T := T) (n := n)) p p' ->
  refines Rseqmultinom m m' ->
  M.MapsTo m' a p' -> p@_m = a.
(** the converse may be wrong if [a = 0] *)
Proof.
move=> Hp Hm HMT; move/F.find_mapsto_iff in HMT.
by rewrite (refine_find_mpoly Hp Hm) /odflt /oapp HMT.
Qed.

Lemma not_In_mcoeff {n} m m' p p' :
  refines (Reffmpoly (T := T) (n := n)) p p' ->
  refines Rseqmultinom m m' ->
  ~ M.In m' p' -> p@_m = 0.
Proof.
move=> Hp Hm Hin; rewrite (refine_find_mpoly Hp Hm).
by move/F.not_find_in_iff: Hin ->.
Qed.

Arguments mpoly_scale {n R} c p.
Global Instance refine_mpoly_scale_eff n :
  refines (eq ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_scale mpoly_scale_eff.
Proof.
apply refines_abstr => c c' ref_c.
apply refines_abstr => p p' ref_p.
rewrite /mpoly_scale_eff; apply: refine_effmpolyP.
{ move=> m /M.map_2 Hm; exact: refine_size_mpoly ref_p _ _. }
move=> m m' ref_m; rewrite mcoeffZ.
case Es: (M.find _ _) => [s|] /=.
{ have /F.find_mapsto_iff/F.map_mapsto_iff [a [-> Ha2 /=]] := Es.
  rewrite (refines_eq ref_c).
  congr *%R.
  apply: MapsTo_mcoeff ref_p ref_m Ha2. }
move/F.not_find_in_iff in Es.
suff->: p@_m = 0 by rewrite GRing.mulr0.
apply: not_In_mcoeff ref_p ref_m _.
move=> K; apply: Es.
exact/F.map_in_iff.
Qed.

Arguments mpoly_add {n R} p q.
Global Instance refine_mpoly_add_eff n :
  refines (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_add mpoly_add_eff.
Proof.
apply refines_abstr => p p' ref_p.
apply refines_abstr => q q' ref_q.
rewrite /mpoly_add_eff.
apply: refine_effmpolyP.
{ move=> m /F.in_find_iff Hm.
  have [Hip'|Hiq'] : M.In m p' \/ M.In m q'.
    rewrite !F.in_find_iff.
    rewrite F.map2_1bis // in Hm.
    case: M.find Hm; case: M.find; try by[left|left|right|].
  apply (@refine_size_mpoly _ _ _ _ ref_p _ Hip').
  apply (@refine_size_mpoly _ _ _ _ ref_q _ Hiq'). }
move=> m m' Hm.
rewrite mcoeffD F.map2_1bis //.
case Ep: M.find => [cp|]; case Eq: M.find => [cq|] /=.
- move/F.find_mapsto_iff in Ep;
  move/F.find_mapsto_iff in Eq;
  by rewrite (MapsTo_mcoeff ref_p Hm Ep) (MapsTo_mcoeff ref_q Hm Eq).
- move/F.find_mapsto_iff in Ep;
  move/F.not_find_in_iff in Eq;
  by rewrite (MapsTo_mcoeff ref_p Hm Ep) (not_In_mcoeff ref_q Hm Eq)
  GRing.addr0.
- move/F.not_find_in_iff in Ep;
  move/F.find_mapsto_iff in Eq;
  by rewrite (not_In_mcoeff ref_p Hm Ep) (MapsTo_mcoeff ref_q Hm Eq)
  GRing.add0r.
- move/F.not_find_in_iff in Ep;
  move/F.not_find_in_iff in Eq;
  by rewrite (not_In_mcoeff ref_p Hm Ep) (not_In_mcoeff ref_q Hm Eq)
  GRing.addr0.
Qed.

Definition mpoly_sub {n} (p : {mpoly T[n]}) q := mpoly_add p (mpoly_opp q).

Global Instance refine_mpoly_sub_eff n :
  refines (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_sub mpoly_sub_eff.
apply refines_abstr => p p' ref_p.
apply refines_abstr => q q' ref_q.
rewrite /mpoly_add_eff.
apply: refine_effmpolyP.
{ move=> m /F.in_find_iff Hm.
  have [Hip'|Hiq'] : M.In m p' \/ M.In m q'.
    rewrite !F.in_find_iff.
    rewrite F.map2_1bis // in Hm.
    case: M.find Hm; case: M.find; try by[left|left|right|].
  apply (@refine_size_mpoly _ _ _ _ ref_p _ Hip').
  apply (@refine_size_mpoly _ _ _ _ ref_q _ Hiq'). }
move=> m m' Hm.
rewrite mcoeffB F.map2_1bis //.
case Ep: M.find => [cp|]; case Eq: M.find => [cq|] /=.
- move/F.find_mapsto_iff in Ep;
  move/F.find_mapsto_iff in Eq;
  by rewrite (MapsTo_mcoeff ref_p Hm Ep) (MapsTo_mcoeff ref_q Hm Eq).
- move/F.find_mapsto_iff in Ep;
  move/F.not_find_in_iff in Eq;
  by rewrite (MapsTo_mcoeff ref_p Hm Ep) (not_In_mcoeff ref_q Hm Eq)
  GRing.subr0.
- move/F.not_find_in_iff in Ep;
  move/F.find_mapsto_iff in Eq;
  by rewrite (not_In_mcoeff ref_p Hm Ep) (MapsTo_mcoeff ref_q Hm Eq)
  GRing.sub0r.
- move/F.not_find_in_iff in Ep;
  move/F.not_find_in_iff in Eq;
  by rewrite (not_In_mcoeff ref_p Hm Ep) (not_In_mcoeff ref_q Hm Eq)
  GRing.subr0.
Qed.

Lemma rem_mpoly_eff n (q p' : effmpoly T) (k' : seqmultinom) (e : T)
  (p : mpoly n T) (k : 'X_{1..n}) :
  ~ M.In k' q -> P.Add k' e q p' -> refines Reffmpoly p p' ->
  refines Rseqmultinom k k' -> refines Reffmpoly (p - p@_k *: 'X_[k]) q.
Proof.
move=> Hin Hadd Hp Hk.
apply refine_effmpolyP.
{ move=> m'' [c' Hc']; move: (Hadd m''); rewrite F.add_o.
  case E.eq_dec.
  { move/mnmc_eq_seqP/eqP <-; rewrite -F.find_mapsto_iff => Hm.
    by apply (@refine_size_mpoly _ _ _ _ (Hp)); exists e. }
  rewrite (proj1 (F.find_mapsto_iff q m'' c')) // => _ H.
  apply (@refine_size_mpoly _ _ _ _ (Hp)).
  by exists c'; move: H; rewrite -F.find_mapsto_iff. }
move=> mm mm' ref_mm; move: (Hadd mm'); rewrite F.add_o.
rewrite mcoeffB mcoeffZ mcoeffX.
case E.eq_dec.
{ move/mnmc_eq_seqP/eqP => Hmm'; rewrite -Hmm'.
  have Hmm : k = mm.
  { by apply/eqP; rewrite (Rseqmultinom_eq Hk ref_mm); apply/eqP. }
  rewrite (proj1 (F.not_find_in_iff _ _) Hin) -Hmm eqxx GRing.mulr1.
  by rewrite (refine_find_mpoly Hp Hk) => ->; rewrite GRing.subrr. }
move=> Hmm' <-.
have Hmm : ~ k = mm.
{ move=> Hmmm; apply/Hmm'/mnmc_eq_seqP.
  by rewrite -(Rseqmultinom_eq Hk ref_mm); apply/eqP. }
rewrite (refine_find_mpoly Hp ref_mm).
by have ->: (k == mm = false); [apply/eqP|rewrite GRing.mulr0 GRing.subr0].
Qed.

Lemma refine_mpoly_sum_eff n k f f' (p : mpoly k T) p' :
  (forall m, f m 0 = 0) ->
  refines (Rseqmultinom ==> eq ==> Reffmpoly (T:=T) (n:=n)) f f' ->
  refines Reffmpoly p p' ->
  refines Reffmpoly (\sum_(m <- msupp p) f m p@_m)
                  (M.fold (fun m c => mpoly_add_eff (f' m c)) p' mp0_eff).
Proof.
move=> Hf ref_f; move: p.
apply P.fold_rec.
{ move=> q' Eq' q Hq.
  suff -> : q = 0; [by rewrite msupp0 big_nil; apply refine_mp0_eff|].
  apply /mpolyP => m.
  rewrite (refine_find_mpoly Hq (refine_seqmultinom_of_multinom m)).
  rewrite mcoeff0; case_eq (M.find (seqmultinom_of_multinom m) q') => [s|->]//.
  rewrite -F.find_mapsto_iff F.elements_mapsto_iff.
  by rewrite -in_InA_eq_key_elt_iff (proj1 (P.elements_Empty _ ) Eq'). }
move=> m' c p'' q q' Hp'' Hq Hq' IH p Hp.
pose m := multinom_of_seqmultinom_val k m'; pose cm := c *: 'X_[m].
have ref_m : refines Rseqmultinom m m'.
{ apply refine_multinom_of_seqmultinom_val.
  move: (Hq' m'); rewrite F.add_eq_o; [|by apply/mnmc_eq_seqP]; move=> Hm'.
  apply (@refine_size_mpoly _ _ _ _ Hp).
  by exists c; apply M.find_2. }
have Hc : p@_m = c.
{ rewrite (refine_find_mpoly Hp ref_m) (Hq' m') F.add_eq_o //.
  apply E.eq_refl. }
pose pmcm := p - cm.
have Hpmcm : pmcm@_m = 0.
{ by rewrite mcoeffB mcoeffZ mcoeffX eqxx Hc GRing.mulr1 GRing.subrr. }
have -> : \sum_(m <- msupp p) f m p@_m
  = f m c + \sum_(m <- msupp pmcm) f m pmcm@_m.
{ case_eq (m \in msupp p) => Hmsuppp.
  { rewrite (big_rem _ Hmsuppp) /= Hc; f_equal.
    rewrite /pmcm /cm -Hc -(perm_big _ (msupp_rem p m)) /=.
    apply eq_big_seq => i.
    rewrite mcoeffB mcoeffZ mcoeffX.
    rewrite mcoeff_msupp Hc -/cm -/pmcm -Hpmcm.
    case (@eqP _ m i) => [->|]; [by rewrite eqxx|].
    by rewrite GRing.mulr0 GRing.subr0. }
  move: Hmsuppp; rewrite /pmcm /cm mcoeff_msupp Hc; move/eqP ->.
  by rewrite Hf GRing.add0r GRing.scale0r GRing.subr0. }
eapply refines_apply.
{ eapply refines_apply; [by apply refine_mpoly_add_eff|].
  eapply refines_apply; [|by apply trivial_refines; symmetry].
  eapply refines_apply; [eapply ref_f|apply ref_m]. }
apply IH.
rewrite /pmcm /cm -Hc.
apply (rem_mpoly_eff Hq Hq' Hp ref_m).
Qed.

Lemma RseqmultinomE {n} m m' :
  refines (Rseqmultinom (n := n)) m m' <=> m = map spec_N m' :> seq nat.
Proof.
split => Hmain.
{ apply eq_from_nth with (x0 := O).
  { by rewrite size_map size_tuple (@refine_size _ m). }
move=> i Hi.
rewrite size_tuple in Hi.
case: n m Hmain Hi => // n m Hmain Hi.
rewrite -(inordK Hi) (nth_map 0%num); last by rewrite (@refine_size _ m).
by rewrite (@refine_nth _ m) -tnth_nth. }
have Hsz : size m' = size m by rewrite Hmain size_map.
apply: refine_seqmultinomP.
{ by rewrite Hsz size_tuple. }
case: n m Hmain Hsz => [|n] m Hmain Hsz; first by case.
by move=> i; rewrite (mnm_nth O) Hmain (nth_map 0%num 0%N) // Hsz size_tuple.
Qed.

Lemma refine_Madd_mnm_add {n} (m : 'X_{1.. n}) m' (c : T) p p' :
  refines Rseqmultinom m m' ->
  refines Reffmpoly p p' ->
  m \notin msupp p ->
  refines Reffmpoly (+%R (c *: 'X_[m]) p) (M.add m' c p').
Proof.
move=> Hm Hp Hnotin.
apply: refine_effmpolyP.
{ move=> k /F.add_in_iff [Hk|Hk].
  - move/mnmc_eq_seqP/eqP: Hk <-.
    apply RseqmultinomE in Hm.
    by rewrite -(size_map spec_N m') -Hm size_tuple.
  - by apply (@refine_size_mpoly _ _ _ _ Hp). }
move=> l l' Hl; rewrite mcoeffD mcoeffZ mcoeffX.
case: (boolP (m == l)) => Heq /=.
{ rewrite GRing.mulr1.
  rewrite F.add_eq_o /=; last first.
  { apply/mnmc_eq_seqP.
    apply RseqmultinomE in Hm.
    apply RseqmultinomE in Hl.
    move/eqP/(congr1 (@tval n nat \o val)) in Heq.
    rewrite /= Hm Hl in Heq.
    exact/eqP/map_spec_N_inj. }
  move/eqP in Heq; rewrite Heq in Hnotin.
  by rewrite memN_msupp_eq0 // GRing.addr0.
}
rewrite GRing.mulr0 GRing.add0r.
rewrite F.add_neq_o /=; last first.
{ apply/mnmc_eq_seqP.
  apply/negbT; rewrite -(@Rseqmultinom_eq _ _ _ _ _ Hm Hl).
  by move/negbTE: Heq ->.
}
rewrite refinesE in Hp.
exact: refine_find_mpoly.
Qed.

Lemma refine_size_add n (k' : seqmultinom) (e : T)
  (p : mpoly n T) (p' : effmpoly T) (q : effmpoly T) :
  P.Add k' e q p' -> refines Reffmpoly p p' ->
  refines Rseqmultinom (multinom_of_seqmultinom_val n k') k'.
Proof.
move=> Hadd Hp.
apply refine_multinom_of_seqmultinom_val.
apply (@refine_size_mpoly _ _ _ _ Hp).
exists e; move: (Hadd k'); rewrite F.add_eq_o; [|by apply E.eq_refl].
apply M.find_2.
Qed.

Lemma refine_Madd_mnm_add_sum n m m' c (p : mpoly n T) p' :
   refines Rseqmultinom m m' ->
   refines (Reffmpoly (T := T) (n := n)) p p' ->
   refines Reffmpoly (\sum_(i2 <- msupp p) (c * p@_i2) *: 'X_[m + i2])
         (M.fold (fun (l' : M.key) (c' : T) => M.add (mnm_add_seq m' l') (c * c')%C) p' M.empty).
Proof.
move=> ref_m; move: p.
apply P.fold_rec.
{ move=> q' Eq' q Hq.
  match goal with
  | [  |- refines Reffmpoly ?pol M.empty ] => suff ->: pol = 0
  end.
  { by apply refine_mp0_eff. }
  apply /mpolyP => l.
  rewrite big1 ?mcoeff0 //.
  move=> i _.
  rewrite (refine_find_mpoly Hq (refine_seqmultinom_of_multinom i)) /=.
  case_eq (M.find (seqmultinom_of_multinom i) q') =>[s|/=].
  - rewrite -F.find_mapsto_iff F.elements_mapsto_iff.
    by rewrite -in_InA_eq_key_elt_iff (proj1 (P.elements_Empty _ ) Eq').
  - by move=> _; rewrite GRing.mulr0 GRing.scale0r.
}
move=> k' e q p'' p''' Hmap Hin Hadd Hind p ref_p.
pose k := multinom_of_seqmultinom_val n k'.
have Hk : refines Rseqmultinom k k'; [by apply (refine_size_add Hadd ref_p)|].
have Hp : p@_k = e.
{ rewrite (refine_find_mpoly ref_p Hk) Hadd F.add_eq_o //.
  exact: E.eq_refl. }
pose p0 := (c * e) *: 'X_[m + k].
pose pmpk := p - p@_k *: 'X_[k].
have Hpmpk : pmpk@_k = 0.
{ by rewrite mcoeffB mcoeffZ mcoeffX eqxx Hp GRing.mulr1 GRing.subrr. }
set sum := \sum_(_ <- _) _.
have->: sum = p0 + \big[+%R/0]_(i2 <- msupp pmpk) ((c * pmpk@_i2) *: 'X_[(m + i2)]).
{ rewrite /sum /pmpk /p0.
  case_eq (k \in msupp p) => Hmsuppp.
  { rewrite (big_rem _ Hmsuppp) /= Hp; f_equal.
    rewrite -Hp -(perm_big _ (msupp_rem p k)) /=.
    apply eq_big_seq => i.
    rewrite mcoeffB mcoeffZ mcoeffX.
    rewrite mcoeff_msupp Hp -Hpmpk.
    case (boolP (k == i)).
    { move/eqP<-; rewrite Hpmpk.
      by rewrite mcoeffB Hp mcoeffZ mcoeffX eqxx GRing.mulr1 GRing.subrr eqxx. }
    by rewrite GRing.mulr0 GRing.subr0. }
  move: Hmsuppp; rewrite mcoeff_msupp Hp; move/eqP ->.
  by rewrite GRing.mulr0 GRing.scale0r GRing.add0r GRing.scale0r GRing.subr0. }
rewrite /p0.
apply refine_Madd_mnm_add.
{ eapply refines_apply; first by eapply refines_apply; tc.
  rewrite /k.
  apply refine_multinom_of_seqmultinom_val.
  apply (@refine_size_mpoly _ _ _ _ ref_p).
  red in Hadd.
  apply/F.in_find_iff.
  rewrite Hadd F.add_eq_o //.
  exact/mnmc_eq_seqP.
}
{ eapply Hind.
  apply (rem_mpoly_eff Hin Hadd ref_p Hk). }
rewrite mcoeff_msupp negbK.
set F' := fun i2 => (c *: 'X_[m]) * (pmpk@_i2 *: 'X_[i2]).
rewrite (eq_bigr F').
{ rewrite -big_distrr /= -mpolyE.
  rewrite (mcoeff_poly_mul _ _ (k:=(mdeg (m + k)).+1)) //.
  rewrite big1 // => k0.
  case (boolP (m == k0.1)).
  { by move/eqP<-; rewrite eqm_add2l; move/eqP <-; rewrite Hpmpk GRing.mulr0. }
  by rewrite mcoeffZ mcoeffX; move /negbTE ->; rewrite GRing.mulr0 GRing.mul0r. }
move=> m'' _; rewrite /F'; rewrite mpolyXD.
rewrite -GRing.scalerAl -GRing.scalerA; f_equal.
by rewrite -[RHS]commr_mpolyX -GRing.scalerAl commr_mpolyX.
Qed.

Arguments mpoly_mul {n R} p q.
Global Instance refine_mpoly_mul_eff n :
  refines (Reffmpoly ==> Reffmpoly ==> Reffmpoly (T := T) (n := n))
  mpoly_mul mpoly_mul_eff.
Proof.
apply refines_abstr => q q' ref_q.
apply refines_abstr => p p' ref_p.
rewrite [mpoly_mul q p]mpolyME big_allpairs.
rewrite /mpoly_mul_eff.
pose f m c := \big[+%R/0]_(i2 <- msupp p) ((c * p@_i2) *: 'X_[(m + i2)]).
pose f' m c := @mult_monomial_eff _ mul_instR m c p'.
now_show (refines Reffmpoly (\sum_(m <- msupp q) f m q@_m)
  (M.fold (fun m c => mpoly_add_eff (f' m c)) q' M.empty)).
apply(*:*) refine_mpoly_sum_eff =>//.
- by move=> m; rewrite /f big1 // => m2 _; rewrite GRing.mul0r GRing.scale0r.
- apply refines_abstr => m m' ref_m.
  apply refines_abstr => c c' ref_c.
  rewrite /f /f' /mult_monomial_eff.
  rewrite {ref_c}(refines_eq ref_c).
  by apply refine_Madd_mnm_add_sum.
Qed.

Definition mpoly_exp {n} (p : {mpoly T[n]}) (n : nat) := p ^+ n.

Global Instance refine_mpoly_exp_eff n :
  refines (Reffmpoly ==> Rnat ==> Reffmpoly (T := T) (n := n))
  mpoly_exp (mpoly_exp_eff (n:=n)).
Proof.
apply refines_abstr => p p' ref_p.
apply refines_abstr => k k' ref_k.
rewrite /mpoly_exp /mpoly_exp_eff.
move/RnatE in ref_k.
have{ref_k}->: k' = implem_N k by rewrite ref_k spec_NK.
rewrite /implem_N bin_of_natE.
elim: k => [|k IHk]; first by rewrite GRing.expr0; apply refine_mp1_eff.
case Ek: k => [|k0].
  by rewrite GRing.expr1 /= -[p]GRing.mulr1; refines_apply.
rewrite GRing.exprS -Ek /= -Pos.succ_of_nat ?Ek //.
rewrite Pos.iter_succ.
refines_apply1.
by rewrite Ek /= Pos.of_nat_succ in IHk.
Qed.

Definition seq_Reffmpoly n k (lq : k.-tuple {mpoly T[n]}) (lq' : seq (effmpoly T)) :=
  ((size lq' = k) * forall i, refines Reffmpoly lq`_i (nth mp0_eff lq' i))%type.

Lemma refine_comp_monomial_eff n k :
  refines (Rseqmultinom ==> eq ==> @seq_Reffmpoly n k ==> Reffmpoly)
  (fun m c lq => mpolyC c * mmap1 (tnth lq) m) (comp_monomial_eff (n:= n)).
Proof.
apply refines_abstr => m m' ref_m.
apply refines_abstr => c c' ref_c.
rewrite refinesE in ref_c; rewrite -{}ref_c {c'}.
apply refines_abstr => lq lq' ref_lq.
rewrite mul_mpolyC /comp_monomial_eff; eapply refines_apply.
{ eapply refines_apply; [apply refine_mpoly_scale_eff|by apply trivial_refines]. }
move: ref_lq; rewrite refinesE /seq_Reffmpoly; move => [sz_lq ref_lq].
elim: k m m' ref_m lq lq' sz_lq ref_lq =>[|k IHk] m m' ref_m lq lq' sz_lq ref_lq.
{ rewrite /mmap1 bigop.big_ord0.
  move: (size0nil sz_lq) => ->; rewrite /zipwith /=; apply refine_mp1_eff. }
move: sz_lq; case_eq lq' => //= q0 lqt' Hlq' sz_lq.
move: (@refine_size _ _ _ ref_m); case_eq m' => //= m0 mt' Hm' sz_m'.
rewrite /foldr /= -/(foldr _ _) /mmap1 bigop.big_ord_recl.
eapply refines_apply; [eapply refines_apply; [by apply refine_mpoly_mul_eff|]|].
{ move: (@refine_nth _ _ _ ord0 ref_m); rewrite Hm' /= => <-.
  refines_apply.
  replace (tnth _ _) with (lq`_O); [|by case lq, tval].
  change q0 with (nth mp0_eff (q0 :: lqt') O); rewrite -Hlq'; apply ref_lq. }
injection sz_lq => {sz_lq} sz_lq; injection sz_m' => {sz_m'} sz_m'.
assert (ref_mt : refines Rseqmultinom (multinom_of_seqmultinom_val k mt') mt').
{ by apply /refine_multinom_of_seqmultinom_val /eqP. }
have Hlq_lq' : forall i : nat,
  refines Reffmpoly [tuple of behead lq]`_i (nth mp0_eff lqt' i).
{ by move=> i; move: (ref_lq i.+1); rewrite Hlq' /=; case tval; elim i. }
move: (IHk _ _ ref_mt [tuple of behead lq] _ sz_lq Hlq_lq').
rewrite refinesE /Reffmpoly /ofun_hrel => ->; f_equal.
apply bigop.eq_big => // i _; f_equal.
{ rewrite tnth_behead; f_equal.
  by apply ord_inj; rewrite inordK //; move: (ltn_ord i). }
move /eqP in sz_m'; move: (refine_multinom_of_seqmultinom_val sz_m') => Hmt'.
move: (@refine_nth _ _ _ i Hmt') => <-.
move: (@refine_nth _ _ _ (inord i.+1) ref_m); rewrite Hm' /=.
rewrite inordK /=; [|by rewrite ltnS]; move=> ->; apply f_equal.
by apply ord_inj; rewrite inordK //; move: (ltn_ord i).
Qed.

Arguments comp_mpoly {n R k} lq p.
Global Instance refine_comp_mpoly_eff n k :
  refines (@seq_Reffmpoly n k ==> Reffmpoly ==> Reffmpoly)
  comp_mpoly (comp_mpoly_eff (n:= n)).
Proof.
apply refines_abstr => lq lq' ref_lq.
apply refines_abstr => p p' ref_p.
rewrite /comp_mpoly /mmap /comp_mpoly_eff.
pose f := fun m c => c%:MP_[n] * mmap1 (tnth lq) m.
rewrite (eq_bigr (fun m => f m p@_m)) //.
apply refine_mpoly_sum_eff.
{ by move=> m; rewrite /f mpolyC0 GRing.mul0r. }
{ apply refines_abstr => m m' ref_m.
  apply refines_abstr => c c'; rewrite refinesE /f => <-.
  change (_ * _) with ((fun lq => c%:MP_[n] * mmap1 (tnth lq) m) lq).
  eapply refines_apply; [|by apply ref_lq].
  change (fun _ => _) with ((fun c lq => c%:MP_[n] * mmap1 (tnth lq) m) c).
  eapply refines_apply; [|by apply trivial_refines; symmetry].
  change (fun _ => _) with ((fun m (c : T) lq => c%:MP_[n] * mmap1 (tnth lq) m) m).
  eapply refines_apply; [apply refine_comp_monomial_eff|apply ref_m]. }
apply ref_p.
Qed.

End effmpoly_theory.

(** ** Part 3: Parametricity *)

Derive Inversion inv_HdRel with
  (forall (A : Type) (eqA : A -> A -> Prop) (x : A) (s : seq A), @HdRel A eqA x s) Sort Prop.

Section effmpoly_parametricity.

Context (A : ringType) (C : Type) (rAC : A -> C -> Type).

Definition M_hrel (m : M.t A) (m' : M.t C) : Type :=
  ((forall k, M.In k m <-> M.In k m')
  * forall k e e', M.MapsTo k e m -> M.MapsTo k e' m' -> rAC e e')%type.

Definition ReffmpolyC {n} := (@Reffmpoly A n \o M_hrel)%rel.

Context `{!zero_of C, !one_of C, !opp_of C, !add_of C, !sub_of C, !mul_of C, !eq_of C}.

Context `{!refines rAC 0 0%C}.
Context `{!refines rAC 1 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{ref_sub : !refines (rAC ==> rAC ==> rAC) sub_instR sub_op}.
Context `{ref_mul : !refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> eq) eqtype.eq_op eq_op}.

Lemma refine_M_hrel_empty : refines M_hrel M.empty M.empty.
Proof.
rewrite refinesE; split.
{ by move=> k; rewrite !F.empty_in_iff. }
by move=> k e e' K; exfalso; apply F.empty_mapsto_iff in K.
Qed.

Lemma refine_M_hrel_add :
  refines (eq ==> rAC ==> M_hrel ==> M_hrel) (@M.add A) (@M.add C).
Proof.
rewrite refinesE => m _ <- a c Hac x x' Hx; split.
{ move=> k; rewrite !F.add_in_iff; split; by rewrite (fst Hx k). }
move=> k e e' H1 H2.
apply add_mapsto_iff_dec in H1.
apply add_mapsto_iff_dec in H2.
move: H1 H2.
case=> [[Hy <-]|[Hy He]].
{ move: Hy; move/mnmc_eq_seqP/eqP->.
  elim=>[[_ <-]|] // []; rewrite -/(E.eq k k) => K; exfalso; apply: K.
  exact: E.eq_refl. }
by case; [elim=> H'; elim (Hy H')|elim=>_; apply (snd Hx)].
Qed.

Lemma refine_M_hrel_singleton :
  refines (eq ==> rAC ==> M_hrel)
     (@singleton A) (@singleton C).
Proof.
apply refines_abstr => k k'; rewrite refinesE => <-.
apply refines_abstr => e e' ref_e.
rewrite /singleton.
eapply refines_apply; [|by apply refine_M_hrel_empty].
eapply refines_apply; [|exact ref_e].
eapply refines_apply; [apply refine_M_hrel_add|by rewrite refinesE].
Qed.

Lemma refine_M_hrel_map :
  refines ((rAC ==> rAC) ==> M_hrel ==> M_hrel) (@M.map A A) (@M.map C C).
Proof.
apply refines_abstr => f f' ref_f.
apply refines_abstr => m m' ref_m.
rewrite refinesE; split.
{ move=> k; rewrite !F.map_in_iff.
  move: ref_m; rewrite refinesE => H'; apply H'. }
move=> k e e' H1 H2.
apply map_mapsto_iff_dec in H1.
apply map_mapsto_iff_dec in H2.
move: H1 H2 => [a Ha] [a' Ha'].
rewrite (proj1 Ha) (proj1 Ha').
apply refinesP; eapply refines_apply; [by apply ref_f|].
move: ref_m (proj2 Ha) (proj2 Ha'); rewrite !refinesE => ref_m.
apply (snd ref_m).
Qed.

Lemma refine_M_hrel_find :
  refines (eq ==> M_hrel ==> option_R rAC) (@M.find A) (@M.find C).
Proof.
apply refines_abstr => k k'; rewrite refinesE => <-.
apply refines_abstr => m m'; rewrite refinesE => ref_m.
rewrite refinesE; case_eq (M.find k m') => [e'|]; case_eq (M.find k m) => [e|] /=.
{ move/F.find_mapsto_iff => H1 /F.find_mapsto_iff => H2.
  by constructor; apply (snd ref_m) with k. }
{ move/F.not_find_in_iff => H' H''; exfalso; apply H'.
  by apply (fst ref_m); rewrite F.in_find_iff H''. }
{ move=> H' /F.not_find_in_iff => H''; exfalso; apply H''.
  apply/(fst ref_m k)/F.in_find_iff.
  by rewrite H'. }
by move=> *; constructor.
Qed.

(* Note: Maybe could be simplified using [map2_ifft] *)
Lemma refine_M_hrel_map2 :
  refines ((option_R rAC ==> option_R rAC ==> option_R rAC) ==> M_hrel ==> M_hrel ==> M_hrel)
    (@M.map2 A A A) (@M.map2 C C C).
Proof.
apply refines_abstr => f f' ref_f.
apply refines_abstr => m1 m1' ref_m1.
apply refines_abstr => m2 m2' ref_m2.
have Hf : forall k, option_R rAC (f (M.find k m1) (M.find k m2))
                      (f' (M.find k m1') (M.find k m2')).
{ move=> k; apply refinesP; eapply refines_apply; [eapply refines_apply|].
  { apply ref_f. }
  { eapply refines_apply; [|by apply ref_m1].
    eapply refines_apply; [apply refine_M_hrel_find|by apply trivial_refines]. }
  eapply refines_apply; [|by apply ref_m2].
  eapply refines_apply; [apply refine_M_hrel_find|by apply trivial_refines]. }
rewrite refinesE; rewrite refinesE in ref_m1, ref_m2; split.
{ move=> k; split.
  { move=> Hk; have Hor := M.map2_2 Hk; move: Hk => [e He].
    apply M.find_1 in He; rewrite (M.map2_1 _ Hor) in He.
    move: (Hf k); rewrite He; case_eq (f' (M.find k m1') (M.find k m2')) => //.
    move=> e' He' _; exists e'; apply M.find_2; rewrite -He'; apply M.map2_1.
      by destruct Hor as [Hk|Hk]; [left; apply ref_m1|right; apply ref_m2].
    by move=> _ K; inversion_clear K. }
  move=> Hk; have Hor := M.map2_2 Hk; move: Hk => [e He].
  apply M.find_1 in He; rewrite (M.map2_1 _ Hor) in He.
  move: (Hf k); rewrite He; case_eq (f (M.find k m1) (M.find k m2)) => //.
  move=> e' He' _; exists e'; apply M.find_2; rewrite -He'; apply M.map2_1.
    by destruct Hor as [Hk|Hk]; [left; apply ref_m1|right; apply ref_m2].
  by move=> _ K; inversion_clear K. }
move=> k e e' He He'; move: (M.find_1 He) (M.find_1 He') (Hf k).
case_eq (M.find k m1) => [e1|] He1.
{ rewrite M.map2_1; [|by left; exists e1; apply M.find_2].
  rewrite M.map2_1; [|by left; apply ref_m1; exists e1; apply M.find_2].
  by rewrite He1 => -> -> H; inversion_clear H. }
case_eq (M.find k m2) => [e2|] He2.
{ rewrite M.map2_1; [|by right; exists e2; apply M.find_2].
  rewrite M.map2_1; [|by right; apply ref_m2; exists e2; apply M.find_2].
  by rewrite He1 He2 => -> -> H; inversion_clear H. }
elim (@map2_2_dec _ _ _ m1 m2 k f); [| |by exists e].
{ by move/MIn_sig=> [e'1 He'1]; apply M.find_1 in He'1; rewrite He'1 in He1. }
by move/MIn_sig=> [e'2 He'2]; apply M.find_1 in He'2; rewrite He'2 in He2.
Qed.

Lemma Sorted_InA_not_lt_hd B (ke h : M.key * B) t :
  Sorted (M.lt_key (elt:=B)) (h :: t) ->
  InA (M.eq_key_elt (elt:=B)) ke (h :: t) ->
  ~ M.lt_key ke h.
Proof.
move: h; elim t => [|h' t' IH] h.
{ move=> _ Hin.
  eapply inv_InA; [move=> _ y l Hy Hlt| |exact: Hin].
  by case: Hlt =><- _ => K; move: (proj1 Hy); apply E.lt_not_eq.
  by move=> _ y l K [_ Hl]; rewrite Hl in K; inversion K. }
move=> HS Hin Hlt.
have Hh := proj2 (Sorted_inv HS); eapply inv_HdRel; last exact: Hh; first done.
move=> _.
eapply inv_InA; last exact: Hin.
intros H y l H0 H1 b l0 H2 H3.
move: Hlt (proj1 H0).
by case: H1 =>-> _; apply E.lt_not_eq.
have HS' := proj1 (Sorted_inv HS).
intros H y l H0 H1 b l0 H2 H3.
case: H3 => H31 H32; rewrite H31 in H2.
apply (IH _ HS'); last by apply E.lt_trans with (1 := Hlt).
by case: H1 => _ <-.
Qed.

Lemma Sorted_InA_tl_lt B (ke h : M.key * B) t :
  Sorted (M.lt_key (elt:=B)) (h :: t) ->
  InA (M.eq_key_elt (elt:=B)) ke t ->
  M.lt_key h ke.
Proof.
move: h; elim t => [|h' t' IH] h; [by move=> _ Hin; inversion Hin|].
move=> HS Hin.
have Hh := proj2 (Sorted_inv HS).
eapply inv_HdRel; last exact: Hh; [done|move=> _ b l Hbl [Hb _]].
rewrite Hb in Hbl.
eapply inv_InA; last exact: Hin; move=> _ y l' Hy [Hy' Hl'].
{ change (M.lt_key _ _) with (E.lt h.1 ke.1).
  by rewrite Hy' in Hy; move: (proj1 Hy); move/mnmc_eq_seqP/eqP => ->. }
apply (E.lt_trans Hbl), IH; first by apply (Sorted_inv HS).
by rewrite -Hl'.
Qed.

Lemma refine_M_hrel_elements :
  refines (M_hrel ==> list_R (prod_R eq rAC))
    (@M.elements A) (@M.elements C).
Proof.
apply refines_abstr => m m'; rewrite !refinesE => ref_m.
set em := M.elements m; set em' := M.elements m'.
have: ((forall k, {e | InA (M.eq_key_elt (elt:=A)) (k, e) em}
                 <=> {e' | InA (M.eq_key_elt (elt:=C)) (k, e') em'})
  * (forall k e e', InA (M.eq_key_elt (elt:=A)) (k, e) em ->
                     InA (M.eq_key_elt (elt:=C)) (k, e') em' -> rAC e e'))%type.
{ split.
  { move=> k; split.
    { move=> [e He].
      have Hkm : M.In k m; [by exists e; apply M.elements_2|].
      have /MIn_sig [e' He'] := proj1 (fst ref_m k) Hkm.
      exists e'; by apply M.elements_1. }
    move=> [e' He'].
    have Hkm' : M.In k m'; [by exists e'; apply M.elements_2|].
    have /MIn_sig [e He] := proj2 (fst ref_m _) Hkm'.
    exists e; by apply M.elements_1. }
  move=> k e e' He He'.
  move: (M.elements_2 He) (M.elements_2 He'); apply (snd ref_m). }
move: (M.elements_3 m) (M.elements_3 m'); rewrite -/em -/em'.
clearbody em em'; move: {m m' ref_m} em em'.
elim=> [|h t IH]; case=> [|h' t'] //=.
{ move/SortedT_dec=> _ _ [Heq _].
  move: (ifft2 (Heq h'.1)); elim.
  { by move=> h'2 /InA_nil. }
  by exists h'.2; apply InA_cons_hd; split; [apply E.eq_refl|]. }
{ move=> _ _ [Heq _]; move: (ifft1 (Heq h.1)); elim.
  { by move=> h2 /InA_nil. }
  by exists h.2; apply InA_cons_hd; split; [apply E.eq_refl|]. }
move=> Sht Sht' [Hht1 Hht2].
have St := proj1 (Sorted_inv Sht); have St' := proj1 (Sorted_inv Sht').
have Hhh' : E.eq h.1 h'.1.
{ apply MultinomOrd.intro_eq; apply/negbTE/negP.
  { move=> Hhh'1.
    have Hh1 : {e | InA (M.eq_key_elt (elt:=A)) (h.1, e) (h :: t)}.
    { by exists h.2; apply InA_cons_hd; split; [apply E.eq_refl|]. }
    have [e' He'] := (ifft1 (Hht1 _) Hh1).
    have Hhh'1' : M.lt_key (h.1, e') h'; [by simpl|].
    by apply (Sorted_InA_not_lt_hd Sht' He'). }
  move=> Hh'h1.
  have Hh1 : {e | InA (M.eq_key_elt (elt:=C)) (h'.1, e) (h' :: t')}.
  { by exists h'.2; apply InA_cons_hd; split; [apply E.eq_refl|]. }
  move: (ifft2 (Hht1 _) Hh1) => [e He].
  have Hh'h1' : M.lt_key (h'.1, e) h; [by simpl|].
  by apply (Sorted_InA_not_lt_hd Sht He). }
constructor 2.
apply: prod_RI.
split; [by move: Hhh' => /mnmc_eq_seqP /eqP|].
{ apply (Hht2 h.1); apply InA_cons_hd.
  { by split; [apply E.eq_refl|]. }
  by move: Hhh' => /mnmc_eq_seqP/eqP->; split; [apply E.eq_refl|]. }
apply (IH _ St St').
constructor=> k; specialize (Hht1 k); specialize (Hht2 k).
{ split.
  { move=> [e He].
    have Ht1 : {e | InA (M.eq_key_elt (elt:=A)) (k, e) (h :: t)}.
    { by exists e; apply InA_cons_tl. }
    case (ifft1 Hht1 Ht1) => e' He'.
    exists e'.
    have /InA_cons[Heq0|//] := He'.
    move: (Sorted_InA_tl_lt Sht He); move /E.lt_not_eq.
    move: Hhh'; move/mnmc_eq_seqP/eqP-> => Heq; exfalso; apply Heq.
    move: (proj1 Heq0); move/mnmc_eq_seqP/eqP => /= ->.
    by apply E.eq_refl. }
  move=> [e' He'].
  have Ht1 : { e' | InA (M.eq_key_elt (elt:=C)) (k, e') (h' :: t')}.
  { by exists e'; apply InA_cons_tl. }
  elim (ifft2 Hht1 Ht1) => e He.
  exists e.
  have /InA_cons[Heq0|//] := He.
  move: (Sorted_InA_tl_lt Sht' He'); move /E.lt_not_eq.
  move: Hhh'; move/mnmc_eq_seqP/eqP<- => Heq; exfalso; apply Heq.
  move: (proj1 Heq0); move/mnmc_eq_seqP/eqP => /= ->.
  by apply E.eq_refl. }
by move=> e e' He He'; apply Hht2; apply InA_cons_tl.
Qed.

Derive Inversion inv_list_R with
  (forall (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (s1 : seq A₁) (s2 : seq A₂),
  @list_R A₁ A₂ A_R s1 s2) Sort Type.

Lemma refine_M_hrel_fold :
  refines
    ((eq ==> rAC ==> M_hrel ==> M_hrel) ==> M_hrel ==> M_hrel ==> M_hrel)
    (@M.fold A _) (@M.fold C _).
Proof.
apply refines_abstr => f f' ref_f.
apply refines_abstr => m m' ref_m.
apply refines_abstr => i i' ref_i.
move: (refines_apply refine_M_hrel_elements ref_m); rewrite !M.fold_1 !refinesE.
move: i i' ref_i; generalize (M.elements m), (M.elements m').
elim=> [|h t IHt]; case=> //=.
- by move=> i i'; rewrite refinesE.
- by move=> a l i i' _ K; inversion K.
- by move=> i i' _ K; inversion K.
move=> h' t' i i' ref_i Hyp.
eapply inv_list_R; last exact: Hyp; try done.
move=> H a c sa sc Heq Heqs [H1 H2] [H3 H4].
eapply IHt.
- refines_apply1; first refines_apply1; first refines_apply1.
  { rewrite !refinesE -H1 -H3; by case: Heq. }
  { rewrite -H1 -H3; by refines_apply1. }
- rewrite -H2 -H4; exact: Heqs.
Qed.

Global Instance refine_filter A' B (rAB : A' -> B -> Type) :
  refines ((rAB ==> eq) ==> list_R rAB ==> list_R rAB)
    filter filter.
Proof.
eapply refines_abstr=> f f' rf.
eapply refines_abstr=> l l' rl.
elim: l l' rl => [|h t IH] l'; rewrite refinesE => rl.
{ inversion rl; apply list_R_nil_R. }
move: rl; case l' => [|h' t'] rl; [by inversion rl|].
inversion rl as [|h_ h'_ Hh t_ t'_ Ht].
rewrite /=.
have ->: f h = f' h'; [by apply refinesP; eapply refines_apply; tc|].
specialize (IH t' (trivial_refines Ht)); rewrite refinesE in IH.
by case (f' h') => //; apply list_R_cons_R.
Qed.

Global Instance ReffmpolyC_list_of_mpoly_eff n :
  refines (@ReffmpolyC n ==>
    list_R (prod_R Rseqmultinom rAC))
    (@list_of_mpoly A n) list_of_mpoly_eff.
Proof.
eapply refines_trans; [|by apply refine_list_of_mpoly_eff|].
{ apply (composable_imply _ _ (R2 := list_R (prod_R eq rAC))).
  rewrite composableE=> l.
  elim: l => [|h t IH].
  { case=> [|h' t']; [by move=>_; apply list_R_nil_R|].
    move=> H; inversion H as [x X]; inversion X as [X0 X1].
    by inversion X0 as [H' Hx|H' Hx]; rewrite -Hx in X1; inversion X1. }
  case=> [|h' t'].
  { move=> H; inversion H as [x X]; inversion X as [X0 X1].
    by inversion X1 as [Hx H'|Hx H']; rewrite -Hx in X0; inversion X0. }
  specialize (IH t'); move=> H.
  case: H => l'' X.
  case: X => X0 X1.
  move: X0 X1; case: l'' => [|h'' t''] X0 X1; [by inversion X0|].
  inversion X0 as [|X X' ref_X Y Y' ref_Y].
  inversion X1 as [|Z Z' ref_Z T T' ref_T].
  inversion ref_X as [x x' ref_x x0 x0' ref_x0'].
  inversion ref_Z as [u u' ref_u v v' ref_v].
  apply list_R_cons_R.
  { apply/prod_RI; split; simpl.
    suff->: u' = x' by [].
    rewrite -[u']/(u',v').1 H10 -[x']/(x', x0').1 H8.
    symmetry.
    by eapply refinesP; refines_apply1.
    suff->: x0 = v by [].
    rewrite -[x0]/(x, x0).2 H7.
    rewrite -[v]/(u, v).2 H9.
    by eapply refinesP; refines_apply1. }
  by apply IH; exists t''; split. }
rewrite /list_of_mpoly_eff.
apply refines_abstr => p p' rp.
eapply refines_apply;
  [|eapply refines_apply; [apply refine_M_hrel_elements|exact rp]].
eapply refines_apply; [by apply refine_filter|].
eapply refines_abstr => mc mc' rmc.
rewrite refinesE; f_equal.
rewrite refinesE in rmc; inversion rmc as [a a' ref_a b b' ref_b].
apply refinesP; tc.
Qed.

Global Instance ReffmpolyC_mp0_eff (n : nat) :
  refines (@ReffmpolyC n) 0 (@mp0_eff C).
Proof.
eapply refines_trans; [by apply composable_comp|by apply refine_mp0_eff|].
apply refine_M_hrel_empty.
Qed.

Global Instance ReffmpolyC_mp1_eff (n : nat) :
  refines (@ReffmpolyC n) 1 (mp1_eff (n:=n)).
Proof.
eapply refines_trans; [by apply composable_comp|by apply refine_mp1_eff|].
rewrite /mp1_eff; eapply refines_apply; [|by tc].
by eapply refines_apply; [apply refine_M_hrel_singleton|apply trivial_refines].
Qed.

Instance composable_imply_id2 :
  forall (A B A' B' C' : Type) (rAB : A -> B -> Type) (R1 : A' -> B' -> Type)
    (R2 : B' -> C' -> Type) (R3 : A' -> C' -> Type),
  composable R1 R2 R3 -> composable (rAB ==> R1)%rel (eq ==> R2)%rel (rAB ==> R3)%rel.
Proof.
intros A0 B A' B' C' rAB R1 R2 R3.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c rABac.
apply: R123; exists (fB c); split; [ exact: RfAB | exact: RfBC ].
Qed.

Global Instance ReffmpolyC_mpvar_eff {n1 : nat} :
  refines (rAC ==> Rnat ==> Rord0 ==> @ReffmpolyC n1)
    mpvar (mpvar_eff (n:=n1)).
Proof.
eapply refines_trans.
eapply composable_imply_id1.
eapply composable_imply_id2.
eapply composable_imply_id2.
by tc.
by eapply refine_mpvar_eff.
rewrite /mpvar_eff.
apply refines_abstr => c c' ref_c.
apply refines_abstr => d d' ref_d.
apply refines_abstr => i i' ref_i.
eapply refines_apply; [|by apply ref_c].
eapply refines_apply; [apply refine_M_hrel_singleton|apply trivial_refines].
by rewrite (refines_eq ref_d) (refines_eq ref_i).
Qed.

Global Instance ReffmpolyC_mpolyC_eff (n : nat) :
  refines (rAC ==> ReffmpolyC) (@mpolyC n A) (mpolyC_eff (n:=n)).
Proof.
eapply refines_trans.
eapply composable_imply_id1; by tc.
by apply refine_mpolyC_eff.
apply refines_abstr => c c' ref_c.
eapply refines_apply; [|by apply ref_c].
rewrite /mpolyC_eff; eapply refines_apply;
  by [apply refine_M_hrel_singleton|apply trivial_refines].
Qed.

Global Instance ReffmpolyC_mpolyX_eff (n : nat) :
  refines (Rseqmultinom ==> ReffmpolyC) (@mpolyX n A) mpolyX_eff.
Proof.
eapply refines_trans; [|by apply refine_mpolyX_eff|].
eapply composable_imply_id2; by tc.
rewrite /mpolyX_eff.
apply refines_abstr => m m' ref_m.
eapply refines_apply; [|by tc].
eapply refines_apply; [apply refine_M_hrel_singleton|apply ref_m].
Qed.

Local Instance refine_M_hrel_mpoly_scale_eff :
  refines (rAC ==> M_hrel ==> M_hrel)
    (@mpoly_scale_eff A *%R) (@mpoly_scale_eff C *%C).
Proof.
rewrite /mpoly_scale_eff.
rewrite refinesE => x x' ref_x p p' [Hp1 Hp2]; split.
{ by move=> k; rewrite !F.map_in_iff. }
move=> k e e'; move=>/map_mapsto_iff_dec [a [Ha1 Ha2]].
move=>/map_mapsto_iff_dec [c [Hc1 Hc2]].
rewrite Ha1 Hc1.
rewrite {1}/mul_op.
eapply refinesP; refines_apply; rewrite refinesE.
by eapply (Hp2 _ _ _ Ha2 Hc2).
Qed.

Global Instance ReffmpolyC_mpoly_scale_eff (n : nat) :
  refines (rAC ==> ReffmpolyC ==> ReffmpolyC)
    (@mpoly_scale n A) mpoly_scale_eff.
Proof. by eapply refines_trans; first eapply composable_imply_id1; tc. Qed.

Local Instance refine_M_hrel_mpoly_add_eff :
  refines (M_hrel ==> M_hrel ==> M_hrel)
    (@mpoly_add_eff A +%R) mpoly_add_eff.
Proof.
rewrite /mpoly_add_eff.
eapply refines_apply; first eapply refine_M_hrel_map2.
rewrite refinesE => a a' ref_a b b' ref_b.
case: ref_a; case: ref_b => *; constructor =>//.
by eapply refinesP; refines_apply.
Qed.

Global Instance ReffmpolyC_mpoly_add_eff (n : nat) :
  refines (ReffmpolyC ==> ReffmpolyC ==> ReffmpolyC)
    (@mpoly_add n A) mpoly_add_eff.
Proof. by eapply refines_trans; first eapply composable_imply; tc. Qed.

Local Instance refine_M_hrel_mpoly_sub_eff :
  refines (M_hrel ==> M_hrel ==> M_hrel)
    (@mpoly_sub_eff A -%R sub_instR) mpoly_sub_eff.
Proof.
rewrite /mpoly_sub_eff.
eapply refines_apply; first eapply refine_M_hrel_map2.
rewrite refinesE => a a' ref_a b b' ref_b.
case: ref_a; case: ref_b => *; constructor =>//.
by eapply refinesP; refines_apply.
by eapply refinesP; refines_apply.
Qed.

Global Instance ReffmpolyC_mpoly_sub_eff (n : nat) :
  refines (ReffmpolyC ==> ReffmpolyC ==> ReffmpolyC)
    (@mpoly_sub A n) mpoly_sub_eff.
Proof. by eapply refines_trans; first eapply composable_imply; tc. Qed.

Local Instance refine_M_hrel_mult_monomial_eff :
  refines (eq ==> rAC ==> M_hrel ==> M_hrel)
    (@mult_monomial_eff A *%R) mult_monomial_eff.
Proof.
rewrite /mult_monomial_eff.
eapply refines_abstr => k k' ref_k.
eapply refines_abstr => d d' ref_d.
eapply refines_abstr => e e' ref_e.
eapply refines_apply.
eapply refines_apply.
eapply refines_apply.
eapply refine_M_hrel_fold.
clear e e' ref_e.
eapply refines_abstr => e e' ref_e.
eapply refines_abstr => f f' ref_f.
eapply refines_abstr => g g' ref_g.
eapply refines_apply. (* FIXME: Use refines_apply *)
eapply refines_apply.
eapply refines_apply.
eapply refine_M_hrel_add.
by rewrite (refines_eq ref_k) (refines_eq ref_e) refinesE.
refines_apply.
done.
done.
exact: refine_M_hrel_empty.
Qed.

(* Really needed to restate this? *)
Local Instance refine_M_hrel_mp0_eff :
  refines M_hrel mp0_eff mp0_eff.
Proof. rewrite /mp0_eff; exact: refine_M_hrel_empty. Qed.

Local Instance refine_M_hrel_mpoly_mul_eff :
  refines (M_hrel ==> M_hrel ==> M_hrel)
    (@mpoly_mul_eff A +%R *%R) mpoly_mul_eff.
Proof.
rewrite /mpoly_mul_eff.
apply refines_abstr => a a' ref_a.
apply refines_abstr => b b' ref_b.
repeat eapply refines_apply.
eapply refine_M_hrel_fold.
eapply refines_abstr => k k' ref_k.
eapply refines_abstr => d d' ref_d.
eapply refines_abstr => e e' ref_e.
refines_apply.
done.
by tc.
Qed.

Global Instance ReffmpolyC_mpoly_mul_eff (n : nat) :
  refines (ReffmpolyC ==> ReffmpolyC ==> ReffmpolyC)
    (@mpoly_mul n A) mpoly_mul_eff.
Proof. by eapply refines_trans; first eapply composable_imply; tc. Qed.

Local Instance refine_M_hrel_mpoly_exp_eff n :
  refines (M_hrel ==> Logic.eq ==> M_hrel)
    (@mpoly_exp_eff _ 1 +%R *%R n) (mpoly_exp_eff (n:=n)).
Proof.
rewrite /mpoly_exp_eff.
apply refines_abstr => m m' ref_m.
apply refines_abstr => k k'; rewrite refinesE => <- {k'}.
rewrite !N2Nat.inj_iter.
move Ek: (N.to_nat k) => nk.
elim: nk {Ek} => [|nk IHnk] /=.
{ rewrite /mp1_eff; eapply refines_apply; [|by tc].
  eapply refines_apply; [apply refine_M_hrel_singleton|by apply trivial_refines]. }
eapply refines_apply; first eapply refines_apply; try by tc.
Qed.

Global Instance ReffmpolyC_mpoly_exp_eff (n : nat) :
  refines (ReffmpolyC ==> Rnat ==> ReffmpolyC)
    (@mpoly_exp A n) (mpoly_exp_eff (n:=n)).
Proof. by eapply refines_trans; first eapply composable_imply; tc. Qed.

Definition seq_ReffmpolyC n k := (@seq_Reffmpoly A n k \o list_R M_hrel)%rel.

Local Instance refine_M_hrel_comp_monomial_eff n :
  refines (Logic.eq ==> rAC ==> list_R M_hrel ==> M_hrel)
    (@comp_monomial_eff A 1 +%R *%R n) (comp_monomial_eff (n:=n)).
Proof.
apply refines_abstr => m m'; rewrite refinesE => <-.
apply refines_abstr => c c' ref_c.
apply refines_abstr => lq lq' ref_lq.
rewrite /comp_monomial_eff.
eapply refines_apply.
{ eapply refines_apply; [apply refine_M_hrel_mpoly_scale_eff|apply ref_c]. }
move: lq lq' ref_lq m.
elim=> [|hlq tlq IH]; case=> [|hlq' tlq']; rewrite refinesE //=.
{ move=> _ m /=; rewrite /mp1_eff; eapply refines_apply; [|by tc].
  eapply refines_apply; [apply refine_M_hrel_singleton|by apply trivial_refines]. }
by move=> K; inversion K.
by move=> K; inversion K.
move=> K; inversion K.
 case=> [|hm tm] /=.
{ rewrite /mp1_eff; eapply refines_apply; [|by tc].
  eapply refines_apply; [apply refine_M_hrel_singleton|by apply trivial_refines]. }
eapply refines_apply; [eapply refines_apply|].
{ by apply refine_M_hrel_mpoly_mul_eff. }
{ eapply refines_apply; [|by apply trivial_refines; symmetry].
  eapply refines_apply; first by apply refine_M_hrel_mpoly_exp_eff.
  apply trivial_refines.
  done. }
by apply IH; rewrite refinesE.
Qed.

Local Instance refine_M_hrel_comp_mpoly_eff (n : nat) :
  refines (list_R M_hrel ==> M_hrel ==> M_hrel)
    (@comp_mpoly_eff A 1 +%R *%R n) (comp_mpoly_eff (n:=n)).
Proof.
rewrite /comp_mpoly_eff.
apply refines_abstr => lq lq' ref_lq.
apply refines_abstr => p p' ref_p.
eapply refines_apply.
eapply refines_apply.
eapply refines_apply.
eapply refine_M_hrel_fold.
eapply refines_abstr => k k' ref_k.
eapply refines_abstr => d d' ref_d.
eapply refines_abstr => e e' ref_e.
refines_apply.
done.
by tc.
Qed.

Global Instance ReffmpolyC_comp_mpoly_eff (n k : nat) :
  refines (seq_ReffmpolyC (k:=k) ==> ReffmpolyC ==> ReffmpolyC)
    (comp_mpoly (k:=n)) (comp_mpoly_eff (n:=n)).
Proof. by eapply refines_trans; first eapply composable_imply; tc. Qed.

End effmpoly_parametricity.

End FMapMultipoly.

(*
Module M := FMapList.Make MultinomOrd.
Module PolyList := FMapMultipoly M.
 *)
Module M := FMapAVL.Make MultinomOrd.
Module PolyAVL := FMapMultipoly M.
