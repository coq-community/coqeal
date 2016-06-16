Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop binomial finset finfun zmodp ssralg countalg finalg poly polydiv.
From mathcomp
Require Import perm fingroup.

From CoqEAL
Require Import hrel pos param refinements binnat boolF2 seqpoly poly_op trivial_seq poly_div boolF2.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import FinRing.Theory.
Import Pdiv.Field.
Import Refinements.Op Poly.Op.
Local Open Scope ring_scope.

Section npoly.

Variable n : nat.
Variable R : ringType.

Record npolynomial : predArgType := Npolynomial {
  poly_of_npoly :> {poly R};
  _ : (size poly_of_npoly <= n.+1)%N
}.

Canonical npoly_subType := [subType for poly_of_npoly].
Definition npoly_eqMixin := Eval hnf in [eqMixin of npolynomial by <:].
Canonical npoly_eqType := Eval hnf in EqType npolynomial npoly_eqMixin.
Definition npoly_choiceMixin := [choiceMixin of npolynomial by <:].
Canonical npoly_choiceType :=
  Eval hnf in ChoiceType npolynomial npoly_choiceMixin.

Definition npoly_of of (phant R) := npolynomial.
Local Notation npoly_ofR := (npoly_of (Phant R)).

Canonical npoly_of_subType := [subType of npoly_ofR].
Definition npoly_of_eqType := [eqType of npoly_ofR].
Definition npoly_of_choiceType := [eqType of npoly_ofR].

End npoly.

Notation "'{poly_' n R }" := (npoly_of n (Phant R))
  (at level 0, n at level 1, format "'{poly_' n  R }").

Section npoly_theory.
Variable n : nat.
Variable R : ringType.

Lemma size_npoly (p : {poly_n R}) : (size p <= n.+1)%N. Proof. exact: valP p. Qed.
Lemma npoly_inj : injective (@poly_of_npoly n R). Proof. exact: val_inj. Qed.

End npoly_theory.
Hint Resolve size_npoly.

Section fin_npoly.

Variable R : finRingType.
Variable n : nat.
Implicit Types p q : {poly_n R}.

Definition npoly_countMixin : Countable.mixin_of {poly_n R} :=
   @sub_countMixin (CountType {poly R} (poly_countMixin [countRingType of R]))
                   _ (npoly_subType n R).
Canonical npoly_countType := Eval hnf in CountType (npolynomial n R) npoly_countMixin.
Canonical npoly_of_countType := [countType of {poly_n R}].
Canonical npoly_subCountType := [subCountType of (npolynomial n R)].
Canonical npoly_of_subCountType := [subCountType of {poly_n R}].

Definition npoly_enum : seq {poly_n R} :=
  pmap insub [seq \poly_(i < n.+1) (f : (R^(_))) (inord i) | f <- enum (R^n.+1)%type].

Lemma npoly_enum_uniq : uniq npoly_enum.
Proof.
rewrite pmap_sub_uniq // map_inj_uniq => [|f g eqfg]; rewrite ?enum_uniq //.
apply/ffunP => /= i; have /(congr1 (fun p : {poly _} => p`_i)) := eqfg.
by rewrite !coef_poly ltn_ord inord_val.
Qed.

Lemma mem_npoly_enum p : p \in npoly_enum.
Proof.
rewrite mem_pmap_sub; apply/mapP.
eexists [ffun i : 'I__ => p`_i]; first by rewrite mem_enum.
apply/polyP => i; rewrite coef_poly.
have [i_small|i_big] := ltnP; first by rewrite ffunE /= inordK.
by rewrite nth_default // 1?(leq_trans _ i_big) // size_npoly.
Qed.

Definition npoly_finMixin :=
  Eval hnf in UniqFinMixin npoly_enum_uniq mem_npoly_enum.
Canonical npoly_finType := Eval hnf in FinType (npolynomial n R) npoly_finMixin.
Canonical npoly_subFinType := Eval hnf in [subFinType of npolynomial n R].
Canonical npoly_of_finType := [finType of {poly_n R}].
Canonical npoly_of_subFinType := [subFinType of {poly_n R}].

Lemma card_npoly : #|{poly_n R}| = (#|R| ^ n.+1)%N.
Proof.
rewrite cardE enumT unlock /= size_pmap_sub.
rewrite (@eq_in_count _ _ predT) ?count_predT; last first.
  by move=> _ /mapP /= [f _ ->]; rewrite size_poly.
by rewrite size_map -cardE card_ffun card_ord.
Qed.

Canonical npoly (E : nat -> R) : {poly_n R} :=
  @Npolynomial _ _ (\poly_(i < n.+1) E i) (size_poly _ _).

Fact size_npoly0 : size (0 : {poly R}) <= n.+1.
Proof. by rewrite size_poly0. Qed.

Definition npoly0 := Npolynomial (size_npoly0).

Definition NPoly (p : {poly R}) : {poly_n R} := insubd npoly0 p.

Definition npoly_of_seq := NPoly \o Poly.

End fin_npoly.

Section Irreducible.

Variable R : finIdomainType.
Variable p : {poly R}.

Definition irreducibleb :=
  ((1 < size p) && [forall q : {poly_((size p).-2) R}, (Pdiv.Ring.rdvdp q p)%R ==> (sizep q <= 1)])%N.

Lemma irreducibleP : reflect (irreducible_poly p) irreducibleb.
Proof.
rewrite /irreducibleb /irreducible_poly.
apply: (iffP idP) => [/andP[sp /'forall_implyP /= Fp]|[sp Fpoly]].
  have sp_gt0 : size p > 0 by case: size sp.
  have p_neq0 : p != 0 by rewrite -size_poly_eq0; case: size sp.
  split => // q sq_neq1 dvd_qp; rewrite -dvdp_size_eqp // eqn_leq dvdp_leq //=.
  apply: contraNT sq_neq1; rewrite -ltnNge => sq_lt_sp.
  have q_small: (size q <= (size p).-2.+1)%N by rewrite prednK -ltnS prednK.
  rewrite Pdiv.Idomain.dvdpE in dvd_qp.
  have /= := Fp (Npolynomial q_small) dvd_qp.
  rewrite leq_eqVlt ltnS => /orP[//|]; rewrite size_poly_leq0 => /eqP q_eq0.
  by rewrite -Pdiv.Idomain.dvdpE q_eq0 dvd0p (negPf p_neq0) in dvd_qp.
have sp_gt0 : size p > 0 by case: size sp.
rewrite sp /=; apply/'forall_implyP => /= q; rewrite -Pdiv.Idomain.dvdpE=> dvd_qp.
have [/eqP->//|/Fpoly/(_ dvd_qp)/eqp_size sq_eq_sp] := boolP (sizep q == 1%N).
by have := size_npoly q; rewrite sq_eq_sp prednK -ltnS prednK ?ltnn.
Qed.

End Irreducible.

(* Section IrreducibleP. *)

(* Variable R : idomainType. *)

(* Implicit Types p q : {poly R}. *)

(* Lemma irreducible_poly_eq p q : irreducible_poly p -> p %= q -> irreducible_poly q. *)
(* Proof. *)
(* move=> [Sp Ip] pEq; split=> [|r Sr Dr]; first by rewrite -(eqp_size pEq). *)
(* apply: eqp_trans (pEq). *)
(* by apply: Ip ; rewrite ?(eqp_dvdr _ pEq). *)
(* Qed. *)

(* Lemma irreducible_polyZ p k : *)
(*    k != 0 -> irreducible_poly p -> irreducible_poly (k *: p). *)
(* Proof. *)
(* by move=> /eqp_scale H /irreducible_poly_eq; apply; rewrite eqp_sym. *)
(* Qed. *)

(* End IrreducibleP.  *)


Local Instance zero_nat : zero_of nat := 0%N.
Local Instance one_nat  : one_of nat  := 1%N.
Local Instance add_nat  : add_of nat  := addn.
Local Instance sub_nat  : sub_of nat  := subn.
Local Instance mul_nat  : mul_of nat  := muln.
Local Instance exp_nat  : exp_of nat nat := expn.
Local Instance leq_nat  : leq_of nat  := ssrnat.leq.
Local Instance lt_nat   : lt_of nat  := ssrnat.ltn.
Local Instance eq_nat   : eq_of nat   := eqtype.eq_op.

Local Instance spec_nat : spec_of nat nat := spec_id.

Local Instance implem_nat : implem_of nat nat := implem_id.

Arguments refines A B R%rel m n.

(* Definition card_type := *)
(*   forall  (S : Type) (T' : Type) (N : Type) (enumT' : S) `{zero_of N} `{one_of N} `{add_of N}, N. *)
(* Parametricity card_type. *)

Section card.
Context (T' : Type) (N : Type).
Context (enumT' : seq T')  `{zero_of N} `{one_of N} `{add_of N}.
Definition card' (P' : pred T') : N := size_op [seq s <- enumT' | P' s].
End card.
Parametricity card'.

Lemma size_seqE T (s : seq T) : (@size_seq _ _ 0%N 1%N addn) s = size s.
Proof. by elim: s => //= x s ->; rewrite [(_ + _)%C]addn1. Qed.

Lemma card'_perm (T : eqType) (s s' : seq T) (P : pred T) :
  perm_eq s s' -> card' s P = card' s' P :> nat.
Proof.
move=> peq_ss'; rewrite /card' /size_op !size_seqE.
by apply/perm_eq_size/perm_eqP=> x; rewrite !count_filter; apply/perm_eqP.
Qed.

Lemma card'E (T : finType) (P : pred T) : card' (@Finite.enum _) P = #|P|.
Proof.
rewrite cardE.
by rewrite -filter_index_enum /index_enum /card' /size_op /= size_seqE.
Qed.
Lemma refines_split T T' T'' (R1 : T -> T' -> Type) (R2 : T' -> T'' -> Type) x z:
  refines (R1 \o R2) x z -> {y : T' & (refines R1 x y * refines R2 y z)%type}. 
Proof. by rewrite !refinesE. Qed.

Lemma refines_split2 T T' T'' (R1 : T -> T' -> Type) (R2 : T' -> T'' -> Type) x z:
  refines (R1 \o R2) x z -> {y : T' & (R1 x y * refines R2 y z)%type}. 
Proof. by rewrite !refinesE. Qed.

Section enumerable.
Context (T : finType) (T' : Type) (RT : T -> T' -> Type).
Variable (N : Type) (rN : nat -> N -> Type).
Context (enumT' : seq T')
  {enumR : refines (perm_eq \o (list_R RT)) (@Finite.enum T) enumT'}.
Context `{zero_of N} `{one_of N} `{add_of N}.
Context `{!refines rN 0%N 0%C}.
Context `{!refines rN 1%N 1%C}.
Context `{!refines (rN ==> rN ==> rN)%rel addn add_op}.
Context (P : pred T) (P' : pred T').

Global Instance refines_card :
  (forall x x' `{!refines RT x x'}, refines (bool_R \o (@unify _)) (P x) (P' x')) ->
  refines rN #|[pred x | P x]| (card' enumT' P').
Proof.
move=> RP; have := refines_comp_unify (RP _ _ _) => /refines_abstr => {RP} RP.
have [s [rs1 rs2]] := refines_split2 enumR.
by rewrite -card'E (@card'_perm _ _ s) //; param card'_R.
Qed.

End enumerable.

Local Open Scope rel_scope.

Section enum_boolF2.

Definition enum_boolF2 : seq bool := [:: false; true].

End enum_boolF2.

Parametricity enum_boolF2.

Global Instance refines_enum_boolF2 :
  refines (perm_eq \o list_R Rbool) (Finite.enum [finType of 'F_2]) (enum_boolF2).
Proof.
eapply refines_trans; tc.
  
Admitted.

Section enum_npoly.

Context (N : Type) (n : N) (A : Type) (P : Type).
Context (iter : forall T, N -> (T -> T) -> T -> T).
Context (enum : seq A) (poly_of_seq : seq A -> P).

Definition enum_npoly : seq P :=
 let extend e := flatten [seq map (cons x) e | x <- enum] in
 map poly_of_seq (iter n extend [::[::]]).

End enum_npoly.

Lemma enum_npolyE (n : nat) (R : finRingType) s :
  perm_eq (Finite.enum R) s ->
  perm_eq (Finite.enum [finType of {poly_n R}])
               (enum_npoly n iter s (@npoly_of_seq _ _)).
Proof.
Admitted.

Parametricity enum_npoly.

Section RnpolyC.

Context (A : finRingType).
Context (C : Type) (rAC : A -> C -> Type).
Context (N : Type) (rN : nat -> N -> Type).
Context (n : nat) (n' : N) `{!refines rN n n'}.
Context (iter' : forall T, N -> (T -> T) -> T -> T)
  {iterR : forall T T' RT, 
    refines (rN ==> (RT ==> RT) ==> RT ==> RT) (@iter T) (@iter' T')}.
Context (enumC : seq C)
  {enumR : refines (perm_eq \o (list_R rAC)) (@Finite.enum A) enumC}.

Definition Rnpoly : {poly_n A} -> {poly A} -> Type :=
  fun p q => p = q :> {poly A}.

Definition RnpolyC : {poly_n A} -> seqpoly C -> Type :=
  (Rnpoly \o (RseqpolyC rAC))%rel.

Global Instance refines_enum_npoly :
   refines (perm_eq \o list_R RnpolyC)
           (Finite.enum [finType of {poly_n A}]) (enum_npoly n' iter' enumC id).
Proof.
have [s [sP ?]] := refines_split2 enumR.
eapply refines_trans; tc.
  by rewrite refinesE; apply/enum_npolyE/sP.
param enum_npoly_R.
Admitted.

Global Instance refines_RnpolyCpoly (x : {poly_n A}) (y : seqpoly C)
       `{!refines RnpolyC x y} : refines (RseqpolyC rAC) (poly_of_npoly x) y.
Admitted.

End RnpolyC.

Parametricity iter.

Global Instance refines_iter T T' RT :
  refines (Rnat ==> (RT ==> RT) ==> RT ==> RT) (@iter T) (@iter T').
Proof.
param iter_R.
Admitted.


Section LaurentsProblem.

Global Instance refines_predn : refines (Rnat ==> Rnat) predn (fun n => (n - 1)%C).
Admitted.

(* Lemma refines_forgetR (T T' : Type) (R R' : T -> T' -> Type) x y : *)
(*    refines R x y -> unify R' R -> refines R' x y. *)
(* Proof. by rewrite !refinesE => ? ->. Qed. *)


Lemma test_irred : irreducible_poly ('X^5 + 'X^2 + 1 : {poly 'F_2}).
Proof.
apply/irreducibleP; rewrite /irreducibleb -[size _]/(sizep _).
rewrite -[[forall _, _]]/(_ == _) /= /Pdiv.Ring.rdvdp.
by CoqEAL.
Qed.


End LaurentsProblem.