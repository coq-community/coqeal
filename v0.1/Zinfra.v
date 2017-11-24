(** This file is partially based on infra.v by Assia Mahboubi *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg seq.
Require Import choice fintype finfun ssrfun bigop.
(* Require Import zint orderedalg orderedzint. *)

Require Import dvdring cdvdring cssralg.

Require Import Coq.ZArith.Zdiv Coq.ZArith.Zabs.

Import GRing.
(* Import OrderedRing.Theory. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.

(* Structures on positive *)

Definition eqp (p q : positive) : bool :=
  match (p ?= q)%positive with Eq => true | _ => false end.

Lemma eqpP : Equality.axiom eqp.
Proof.
  move=> p q; apply: (iffP  idP)=>[|<-]; last by rewrite /eqp Pos.compare_refl.
  rewrite /eqp; case e: (p ?= q)%positive=> // _; exact: Pcompare_Eq_eq.
Qed.

(* For Coq <= 8.3 *)
(*
Definition eqp (p q : positive) : bool :=
 match ((p ?= q) Eq)%positive with Eq => true | _ => false end.

Lemma eqpP : Equality.axiom eqp.
Proof.
  move=> p q; apply: (iffP  idP)=>[|<-]; last by rewrite /eqp Pcompare_refl.
  rewrite /eqp; case e: ((p ?= q) Eq)%positive=> // _; exact: Pcompare_Eq_eq.
Qed.
*)

Canonical Structure eqp_Mixin := EqMixin eqpP.
Canonical Structure eqp_eqType := Eval hnf in EqType positive eqp_Mixin.

Definition p_unpickle n := Some (Ppred (P_of_succ_nat n)).

Lemma p_pick_cancel : pcancel nat_of_P p_unpickle.
Proof.
  move=> x; rewrite /p_unpickle; congr Some.
  by rewrite pred_o_P_of_succ_nat_o_nat_of_P_eq_id.
Qed.

Definition p_countMixin  := CountMixin p_pick_cancel.
Definition p_choiceMixin := CountChoiceMixin p_countMixin.

Canonical Structure p_choiceType :=
  Eval hnf in ChoiceType positive p_choiceMixin.
Canonical Structure p_countType :=
  Eval hnf in CountType positive p_countMixin.

(* Structures on Z *)
Lemma eqzP : Equality.axiom Zeq_bool.
Proof. by move=> z1 z2;  apply: (iffP idP); move/Zeq_is_eq_bool. Qed.

Canonical Structure Z_Mixin := EqMixin eqzP.
Canonical Structure Z_eqType := Eval hnf in EqType Z Z_Mixin.

Definition z_code (z : Z) :=
  match z with
    |0%Z => (0%nat, true)
    |Zpos p => (pickle p, true)
    |Zneg p => (pickle p, false)
  end.

Definition z_pickle z := pickle (z_code z).

Definition z_decode c :=
  match c with
    |(0%nat, true) => Some 0%Z
    |(0%nat, false) => None
    |(n, true) =>
      if (unpickle n) is Some p then Some (Zpos p) else None
    |(n, false) =>
      if (unpickle n) is Some p then Some (Zneg p) else None
  end.

Definition z_unpickle n :=
  match (unpickle n) with
    |None => None
    |Some u => z_decode u
  end.

Lemma z_codeK : pcancel z_code z_decode.
Proof.
  rewrite /z_code /z_decode.
  case=> // n; case e : (pickle n)=>[|m]; rewrite -?e ?pickleK //;
    by move/ltP: (lt_O_nat_of_P n); rewrite -e -[pickle]/nat_of_P ltnn.
Qed.

Lemma z_pick_cancel : pcancel z_pickle z_unpickle.
Proof.
  by move=> x; rewrite /z_pickle /z_unpickle pickleK z_codeK.
Qed.

Definition z_countMixin  := CountMixin z_pick_cancel.
Definition z_choiceMixin := CountChoiceMixin z_countMixin.

Canonical Structure z_choiceType :=
  Eval hnf in ChoiceType Z z_choiceMixin.
Canonical Structure z_countType :=
  Eval hnf in CountType Z z_countMixin.

Lemma ZplusA : associative Zplus.
Proof. exact Zplus_assoc. Qed.

Lemma ZplusC : commutative Zplus.
Proof. exact Zplus_comm. Qed.

Lemma Zplus0 : left_id (0%Z) Zplus.
Proof. exact Zplus_0_l. Qed.

Lemma ZplusNr : left_inverse  0%Z Zopp Zplus.
Proof. exact Zplus_opp_l. Qed.

Lemma ZplusrN : right_inverse 0%Z Zopp Zplus.
Proof. exact Zplus_opp_r. Qed.

Definition Z_zmodMixin :=
  ZmodMixin ZplusA ZplusC Zplus0 ZplusNr.

Canonical Structure Z_zmodType :=
  Eval hnf in ZmodType Z Z_zmodMixin.

(* Z Ring *)
Lemma ZmultA : associative Zmult.
Proof. exact: Zmult_assoc. Qed.

Lemma Zmult1q : left_id 1%Z Zmult.
Proof. exact: Zmult_1_l. Qed.

Lemma Zmultq1 : right_id 1%Z Zmult.
Proof. exact: Zmult_1_r. Qed.

Lemma Zmultq0 : forall (q : Z), Zmult q 0%Z = 0%Z.
Proof. exact: Zmult_0_r. Qed.

Lemma Zmult_addl : left_distributive Zmult Zplus.
Proof. exact: Zmult_plus_distr_l. Qed.

Lemma Zmult_addr : right_distributive Zmult Zplus.
Proof. exact: Zmult_plus_distr_r. Qed.

Lemma nonzeroZ1 : 1%Z != 0%Z.
Proof. by []. Qed.

Definition Z_ringMixin :=
  RingMixin ZmultA Zmult1q Zmultq1 Zmult_addl Zmult_addr nonzeroZ1.

Canonical Structure Z_ringType :=
  Eval hnf in RingType Z Z_ringMixin.

Lemma ZmultC : commutative Zmult.
Proof. exact: Zmult_comm. Qed.

Canonical Structure Z_comRingType := ComRingType Z ZmultC.

(* Warning : an antisymmetric an a transitive predicates are
present in loaded Relations.Relation_Definition *)
Lemma Zle_bool_antisymb : ssrbool.antisymmetric  Zle_bool.
Proof. by move=> x y; case/andP=> h1 h2; apply: Zle_bool_antisym. Qed.

Lemma Zle_bool_transb : ssrbool.transitive Zle_bool.
Proof. move=> x y z; exact: Zle_bool_trans. Qed.

Lemma Zle_bool_totalb : total Zle_bool.
Proof. by move=> x y; case: (Zle_bool_total x y)=> -> //; rewrite orbT. Qed.

Lemma Zle_bool_addr : forall z x y, Zle_bool x y -> Zle_bool (x + z) (y + z).
Proof. by move=> x y z h; rewrite Zle_bool_plus_mono // Zle_bool_refl. Qed.

Lemma Zle_bool_mulr : forall x y,
  Zle_bool 0 x -> Zle_bool 0 y -> Zle_bool 0 (x * y).
Proof.
move=> x y; move/Zle_is_le_bool=> px; move/Zle_is_le_bool=> py.
by apply/Zle_is_le_bool; apply: Zmult_le_0_compat.
Qed.

Definition Zunit := pred2 1%Z (-1)%Z.

Definition Zinv (z : Z) := z.


Lemma ZmulV : {in Zunit, left_inverse 1%R Zinv *%R}.
Proof. by move=> x; rewrite inE; case/pred2P => ->. Qed.

(* Zmult_1_inversion_r does not exist *)
Lemma unitZPl : forall x y, y * x = 1 -> Zunit x.
Proof. by move=> x y; rewrite mulrC => /Zmult_1_inversion_l [] ->. Qed.

Lemma  Zinv_out : {in predC Zunit, Zinv =1 id}.
Proof. exact. Qed.

Definition Z_comUnitRingMixin :=  ComUnitRingMixin ZmulV unitZPl Zinv_out.

Canonical Structure Z_unitRingType :=
  Eval hnf in UnitRingType Z Z_comUnitRingMixin.

Canonical Structure Z_comUnitRing := Eval hnf in [comUnitRingType of Z].

Lemma Z_idomain_axiom : forall x y : Z,
  x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> x y; rewrite -[x * y]/(Zmult x y); move/Zmult_integral; case=> -> //=.
by rewrite eqxx orbT.
Qed.

Canonical Structure Z_iDomain := Eval hnf in IdomainType Z Z_idomain_axiom.

(* Definition Z_OrderedRingMixin := *)
(*   OrderedRing.Mixin  *)
(*   Zle_bool_antisymb Zle_bool_transb Zle_bool_totalb Zle_bool_addr Zle_bool_mulr. *)

(* Canonical Structure Z_oIdomainType :=  *)
(*   Eval hnf in OIdomainType Z Z_OrderedRingMixin. *)

(* Computable ring structure *)
Definition zid : Z -> Z := @id Z.

Definition Z_czMixin := id_Mixins.id_czMixin [zmodType of Z].

Canonical Structure Z_czType :=
  Eval hnf in CZmodType Z Z Z_czMixin.

(* This does not work:

Definition Z_cringMixin := id_Mixins.id_cringMixin [ringType of Z].

Canonical Structure Z_cringType :=
  Eval hnf in CRingType [ringType of Z] Z_cringMixin.

Eval compute in (mul 3%Z 4%Z).
*)

Lemma Z1 : zid 1%Z = 1%Z.
Proof. by []. Qed.

Lemma zmulP : {morph zid : x y / x * y >-> x * y}.
Proof. by []. Qed.

Definition Z_cringMixin := @CRingMixin [ringType of Z] [czmodType Z of Z]
  1%Z (fun x y => x * y)%Z Z1 zmulP.

Canonical Structure Z_cringType :=
  Eval hnf in CRingType [ringType of Z] Z_cringMixin.

Lemma unitZ : forall x, Zunit x = Zunit (zid x).
Proof. by []. Qed.

Lemma invZ : {morph zid : x / Zinv x >-> Zinv x}.
Proof. by []. Qed.

Definition Z_cunitRingMixin := @CUnitRingMixin [unitRingType of Z] [cringType Z of Z]
  Zunit Zinv unitZ invZ.

Canonical Structure Z_cunitRingType :=
  Eval hnf in CUnitRingType [unitRingType of Z] Z_cunitRingMixin.


(* Divisibility theory for Z *)
Section Zdiv.

Import ssrnat.

Lemma Zabs_mull : forall (a b : Z), a != 0 -> (Zabs_nat b <= Zabs_nat (a * b)%R)%N.
Proof.
move=> a b a0.
rewrite Zabs_nat_mult leq_pmull //.
apply/leP; apply: inj_lt_rev.
rewrite inj_Zabs_nat=> /=.
case: (Zabs_spec a).
  case=> H0a ->.
  move/eqP: a0; move/not_Zeq; case=> // Ha0.
  by move: (Zle_lt_trans 0 a 0 H0a Ha0); move/Zlt_not_eq; move/eqP.
case=> H0a ->; move/eqP: a0; move/not_Zeq.
case; first by rewrite -{1}[a]add0r {1}Zlt_plus_swap.
by move: H0a; move/Zgt_lt=> a0 b0; move: (Zlt_trans a 0 a a0 b0); move/Zlt_not_eq.
Qed.

Definition Zdiv (a b : Z) : (Z * Z) := if b == 0 then (0%Z,a) else Zdiv_eucl a b.

Import Omega.

Lemma ZdivP : forall (a b : Z), EuclideanRing.edivr_spec Zabs_nat a b (Zdiv a b).
Proof.
move=> a b; rewrite /Zdiv.
case b0: (b == 0).
  constructor; first by rewrite mul0r add0r.
  by apply/implyP; move/negP; rewrite b0.
have := (@Z_div_mod_full a b _); case: Zdiv_eucl => q r.
case; first by move/eqP; rewrite b0.
constructor; first by rewrite a0 mulrC.
apply/implyP=> _; move: b1; rewrite /Remainder.
case=> [lt0rb | [ ltbr ler0 ] ]; first by apply/ltP; apply: Zabs_nat_lt.
apply/ltP; apply: inj_lt_rev.
rewrite !inj_Zabs_nat -Zabs_Zopp -[Zabs b]Zabs_Zopp -!inj_Zabs_nat.
by apply: inj_lt; apply: Zabs_nat_lt; omega.
Qed.

Definition Z_euclidMixin := EuclideanRing.Mixin Zabs_mull ZdivP.

Definition Z_dvdMixin := EuclidDvdMixin Z Z_euclidMixin.
Canonical Structure Z_dvdRingType := DvdRingType Z Z_dvdMixin.

Definition Z_gcdMixin := EuclidGCDMixin Z Z_euclidMixin.
Canonical Structure Z_gcdType := GcdRingType Z Z_gcdMixin.

Definition Z_bezoutMixin := EuclidBezoutMixin Z Z_euclidMixin.
Canonical Structure Z_bezoutType := BezoutRingType Z Z_bezoutMixin.

Definition Z_priMixin := EuclidPriMixin Z Z_euclidMixin.
Canonical Structure Z_priType := PriRingType Z Z_priMixin.

Canonical Structure Z_euclidType := EuclidRingType Z Z_euclidMixin.

Lemma zabs : forall (x : Z), Zabs_nat (zid x) = Zabs_nat x.
Proof. by []. Qed.

Lemma zdiv : forall x y, Zdiv (zid x) (zid y) = (zid (Zdiv x y).1, zid (Zdiv x y).2).
Proof.
move=> x y /=.
rewrite /Zdiv /zid /=.
case: ifP => //=.
by case: Zdiv_eucl.
Qed.

Definition Z_ceuclidRingMixin := @CEuclidRingMixin _ _ Zabs_nat _ zabs zdiv.

Canonical Structure Z_ceuclidRingType :=
  Eval hnf in CEuclidRingType [euclidRingType of Z] Z_ceuclidRingMixin.

(* This should be enough the build the other structures! *)

Lemma ZCDvd : forall (x y : Z), omap zid (x %/? y) = ((zid x) %/? (zid y)).
Proof.
rewrite /zid.
move=> x y.
by case: (x %/? y).
Qed.

Definition Z_cdvdRingMixin := CDvdRingMixin ZCDvd.

Canonical Structure Z_cdvdRingType :=
  Eval hnf in CDvdRingType [dvdRingType of Z] Z_cdvdRingMixin.

Lemma ZCGcd : {morph zid : x y / gcdr x y >-> gcdr x y}.
Proof. by []. Qed.

Definition Z_cgcdRingMixin := CGcdRingMixin ZCGcd.

Canonical Structure Z_cgcdRingType :=
  Eval hnf in CGcdRingType [gcdRingType of Z] Z_cgcdRingMixin.

Lemma ZCBezout : forall x y, (zid (bezout x y).1,zid (bezout x y).2) =
                             bezout (zid x) (zid y).
Proof. by move=> x y; case: (bezout x y). Qed.

Definition Z_cbezoutRingMixin := CBezoutRingMixin ZCBezout.

Canonical Structure Z_cbezoutRingType :=
  Eval hnf in CBezoutRingType [bezoutRingType of Z] Z_cbezoutRingMixin.

End Zdiv.


(*
Section Zintdiv.

Local Open Scope ring_scope.

Lemma absz_mull : forall a b, a != 0 -> (absz b <= absz (a * b)%R)%N.
Proof.
move=> a b a0; rewrite -lez_nat -!absrz absr_mul ler_epmull ?absr_ge0 //.
rewrite absrz; move: a0; rewrite -absz_eq0; case: (absz a)=> //.
Qed.

Definition edivz a b :=
  let (q,r) := edivn (absz a) (absz b) in
  if (a >= 0)
     then (q%:Z *~ sgr b, r%:Z)
     else if r == 0%N then (q%:Z *~ -sgr b,0) else ((q%:Z + 1) *~ -sgr b, `|b| - r%:Z).

Lemma edivzP : forall a b, EuclideanRing.edivr_spec absz a b (edivz a b).
Proof.
move=> a b.
rewrite /edivz.
case: edivnP=> q r Ha Hr; case: lerP=> a0 /=.
  constructor; last by rewrite abszE -absr_gt0 absrz ltz_nat.
  by rewrite mulrzAl -mulrzAr -absr_dec -[a]ger0_abs // !absrz Ha addzM mulzM.
case: ifP=> r0; constructor.
* rewrite mulrzAl -mulrzAr mulrNz -absr_dec absrz addr0 mulrN.
  apply: (canRL (@opprK _)).
  by rewrite -ler0_abs ?(ltrW _) // !absrz Ha addzM mulzM (eqP r0) addr0.
* by rewrite -lez_nat -add1n addzM -absrz absr0 lez_nat lt0n absz_eq0 implybb.
* rewrite mulrNz mulNr mulrzAl -mulrzAr -absr_dec mulr_addl mul1r oppr_add.
  rewrite -addrA addKr -oppr_add.
  apply: (canRL (@opprK _)).
  by rewrite -ler0_abs ?(ltrW _) // !absrz Ha addzM mulzM.
rewrite -ltz_nat -!absrz.
apply/implyP=> b0.
rewrite ger0_abs; first by rewrite ltr_subl_addl ltr_addr ltz_nat lt0n r0.
rewrite ler_subr_addr addr0 absrz ltrW // ltz_nat.
by move/implyP: Hr; apply; rewrite lt0n absz_eq0.
Qed.

Definition zint_euclidMixin := EuclideanRing.Mixin absz_mull edivzP.

Definition zint_dvdMixin := EuclidDvdMixin zint zint_euclidMixin.
Canonical Structure zint_dvdRingType := DvdRingType zint zint_dvdMixin.

Definition zint_gcdMixin := EuclidGcdMixin zint zint_euclidMixin.
Canonical Structure zint_gcdType := GcdRingType zint zint_gcdMixin.

Definition zint_bezoutMixin := EuclidBezoutMixin zint zint_euclidMixin.
Canonical Structure zint_bezoutType := BezoutRingType zint zint_bezoutMixin.

Definition zint_priMixin := EuclidPriMixin zint zint_euclidMixin.
Canonical Structure zint_priType := PriRingType zint zint_priMixin.

Canonical Structure zint_euclidType := EuclidRingType zint zint_euclidMixin.

Time Eval compute in 3%:Z %| 4.
Time Eval compute in 2342%:Z %/ 123.
Time Eval compute in (42%:Z * 13 * 7 * 3).
Time Eval compute in (42%:Z * 17 * 2).
Time Eval compute in (gcdr 11466%:Z 1428).
(* Time Eval compute in (gcdr 114662%:Z 14282). *)
End Zintdiv.
*)
