(** This files is based on infra.v written by Assia Mahboubi *)
Require Import QArith.
Require Import Qcanon.
Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import choice fintype finfun ssrfun bigop ssralg.
Require Import cssralg dvdring cdvdring Zinfra.
(* Require Import orderedalg. *)

Close Scope Q_scope.

Set   Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensives.

Import GRing.

Open Local Scope ring_scope.

(* -------------------------------------------------------------------- *)
(* Various eqtype, subtype, choice, count canonical structures          *)
(*               from the standard library                              *)
(* -------------------------------------------------------------------- *)

(* Basic tructures for rational numbers.*)

Definition eqq (x y : Q) : bool :=
  match x, y with
    | (xn # xd)%Q, (yn # yd)%Q => (xn == yn) && (xd == yd)
  end.

Lemma eqq_refl : forall q, eqq q q.
Proof. by move=> [d n]; rewrite /eqq; rewrite 2!eqxx. Qed.

Lemma eqqP : Equality.axiom eqq.
Proof.
  move=> q1 q2; apply: (iffP idP) => [|<-]; last exact: eqq_refl.
  by case: q1=> n1 d1; case: q2=> n2 d2; case/andP; move/eqP->; move/eqP->.
Qed.

Canonical Structure eqq_eqMixin := EqMixin eqqP.
Canonical Structure eqq_eqType := Eval hnf in EqType Q eqq_eqMixin.

Definition q_code (q : Q) :=
  match q with
    |(qnum # qden)%Q => (qnum, qden)
  end.

Definition q_pickle q := pickle (q_code q).

Definition q_decode c :=
  match c with
    |(q, d) => Some (q # d)%Q
  end.

Definition q_unpickle n :=
  match (unpickle n) with
    |None => None
    |Some u => q_decode u
  end.

Lemma q_codeK : pcancel q_code q_decode.
Proof. by move=> []. Qed.

Lemma q_pick_cancel : pcancel q_pickle q_unpickle.
Proof.
by move=> x; rewrite /q_pickle /q_unpickle pickleK q_codeK.
Qed.

Definition q_countMixin  := CountMixin q_pick_cancel.
Definition q_choiceMixin := CountChoiceMixin q_countMixin.

Canonical Structure q_choiceType :=
  Eval hnf in ChoiceType  Q q_choiceMixin.
Canonical Structure q_countType :=
  Eval hnf in CountType Q q_countMixin.

(*
Definition nnegqb (q : Q) :=
  match q with
    (qd # qn)%Q => match qd with Zneg _ => false | _ => true end
  end.
*)


(* Basic and algebraic structures for normalized rational numbers,
we do not intend to be specially clever wrt normalization at this point *)

Record Qcb : Type := QcbMake { qcb_val :> Q; _ : Qred qcb_val == qcb_val }.

Canonical Structure qcb_subType :=
  Eval hnf in [subType for qcb_val by Qcb_rect].

Definition qcb_eqMixin := Eval hnf in [eqMixin of qcb_subType by <:].
Canonical Structure qcb_eqType  := Eval hnf in EqType Qcb qcb_eqMixin.

Definition qcb_choiceMixin := [choiceMixin of Qcb by <:].
Canonical Structure qcb_choiceType :=
  Eval hnf in ChoiceType Qcb  qcb_choiceMixin.

Definition qcb_countMixin := [countMixin of Qcb by <:].
Canonical Structure qcb_countType :=
  Eval hnf in CountType Qcb qcb_countMixin.

Canonical Structure qcb_subCountType :=
  Eval hnf in [subCountType of Qcb].

(* Properties about Qred, Q and Qcb and equalities over all these types *)
Lemma Qredb_involutive : forall q, Qred (Qred q) == (Qred q).
Proof. by move=> q; apply/eqP; apply Qred_involutive. Qed.

(*
Lemma Qcb_is_canon : forall (q q' : Qcb), (q == q')%Q -> q = q'.
Proof.
move=> [x hx] [y hy]; move/Qred_complete=> /=; rewrite (eqP hx) (eqP hy)=> e.
by apply:val_inj.
Qed.
*)

Lemma Qredb_complete : forall q q', (q == q')%Q -> Qred q == Qred q'.
Proof. by move=> q q' H; apply/eqP; apply Qred_complete. Qed.

Lemma Qcb_QeqP : forall (q q': Qcb), reflect (q == q')%Q (q == q').
Proof.
move=> [q Hq] [q' Hq']; apply: (iffP eqP)=> [|]; first by move->.
by move/Qred_complete=> H; apply: val_inj=> /=; rewrite -(eqP Hq) -(eqP Hq').
Qed.

Lemma Qcb_is_canon : forall (q q' : Qcb), (q == q')%Q -> q == q'.
Proof.
  case=> q Hq; case=> q' Hq'; rewrite eqE /= => H.
  by rewrite -(eqP Hq) -(eqP Hq'); apply Qredb_complete.
Qed.

(* Arithmetic over Qcb from the one over Q *)
Definition Q2Qcb (q:Q) : Qcb := QcbMake (Qredb_involutive q).
Arguments Scope Q2Qc [Q_scope].

Definition Qcbplus  (x y : Qcb) := Q2Qcb (x + y).
Definition Qcbmult  (x y : Qcb) := Q2Qcb (x * y).
Definition Qcbopp   (x   : Qcb) := Q2Qcb (- x).
Definition Qcbminus (x y : Qcb) := Q2Qcb (x - y).
Definition Qcbinv   (x   : Qcb) := Q2Qcb (/x).
Definition Qcbdiv   (x y : Qcb) := Q2Qcb (x */ y).

(* just for the tactic *)
Lemma qcb_valE : forall x Hx, qcb_val (@QcbMake x Hx) = x .
Proof . by [] . Qed .

Tactic Notation "qcb" tactic(T) :=
    repeat case=> ? ?;
      apply/eqP; apply Qcb_is_canon;
      rewrite !qcb_valE; repeat setoid_rewrite Qred_correct;
      by T.


Lemma QcbplusA : associative Qcbplus.
Proof.
case=> [x hx] [y hy] [z hz]; apply: val_inj; apply: Qred_complete.
rewrite /= -/(Qred (Qplus y z)) -/(Qred (Qplus x y)).
repeat setoid_rewrite Qred_correct; ring.
Qed.


Lemma QcbplusC : commutative Qcbplus.
Proof.
case=> [x hx] [y hy]; apply: val_inj; apply: Qred_complete.
by rewrite Qplus_comm.
Qed.

Lemma Qcbplus0q : left_id (Q2Qcb 0) Qcbplus.
case=> [x hx];  apply: val_inj; rewrite /= -/(Qred (Qplus 0 x)).
rewrite -{2}(eqP hx). apply: Qred_complete.
by rewrite Qplus_0_l.
Qed.

Lemma QcbplusNq : left_inverse (Q2Qcb 0) Qcbopp Qcbplus.
Proof. by qcb ring. Qed.

Lemma QcbplusqN : right_inverse (Q2Qcb 0) Qcbopp Qcbplus.
Proof. by qcb ring. Qed.

Definition Qcb_zmodMixin :=
  ZmodMixin QcbplusA QcbplusC Qcbplus0q QcbplusNq.


Canonical Structure Qcb_zmodType :=
  Eval hnf in ZmodType Qcb Qcb_zmodMixin.

(* Q/== ==> Ring *)
Lemma QcbmultA : associative Qcbmult.
Proof. by qcb ring. Qed.

Lemma Qcbmult1q : left_id (Q2Qcb 1) Qcbmult.
Proof. by qcb ring. Qed.

Lemma Qcbmultq1 : right_id (Q2Qcb 1) Qcbmult.
Proof. by qcb ring. Qed.

Lemma Qcbmultq0 : forall (q : Qcb), Qcbmult q (Q2Qcb 0) = (Q2Qcb 0).
Proof. by qcb ring. Qed.

Lemma Qcbmult_addl : left_distributive Qcbmult Qcbplus.
Proof. by qcb ring. Qed.

Lemma Qcbmult_addr : right_distributive Qcbmult Qcbplus.
Proof. by qcb ring. Qed.

Lemma nonzeroq1 : Q2Qcb 1 != Q2Qcb 0.
Proof. by rewrite /Q2Qcb eqE /=. Qed.

Definition Qcb_ringMixin :=
  RingMixin QcbmultA Qcbmult1q Qcbmultq1 Qcbmult_addl Qcbmult_addr nonzeroq1.
Canonical Structure Qcb_ringType :=
  Eval hnf in RingType Qcb Qcb_ringMixin.

(* Q/== ==> commutative ring *)
Lemma QcbmultC : commutative Qcbmult.
Proof. by qcb ring. Qed.

Canonical Structure Qcb_comRingType := ComRingType Qcb QcbmultC.

(* Q/== ==> ring with units *)
Lemma Qcb_mulVx :
    forall x:Qcb, x != (Q2Qcb 0) -> Qcbmult (Qcbinv x) x = (Q2Qcb 1).
Proof.
  case=> x Hx; move=> H; apply/eqP; apply Qcb_is_canon.
  rewrite QcbmultC !qcb_valE; repeat setoid_rewrite Qred_correct.
  by apply Qmult_inv_r => Hx0; case/Qcb_QeqP: H.
Qed.

Lemma Qcb_mulxV :
    forall x:Qcb, x != (Q2Qcb 0) -> Qcbmult x (Qcbinv x) = (Q2Qcb 1).
Proof.
  by move=> x Hx; rewrite QcbmultC; apply Qcb_mulVx.
Qed.

Definition Qcb_unit : pred Qcb := fun q:Qcb => q != (Q2Qcb 0).

Lemma Qcb_intro_unit :
    forall (p q : Qcb), Qcbmult q p = (Q2Qcb 1) -> p != (Q2Qcb 0).
Proof.
  move=> p q H; apply/negP; move/eqP => p0.
  by rewrite p0 Qcbmultq0 in H.
Qed.

Lemma Qcb_intro_unit_nC :
    forall (p q : Qcb),
      Qcbmult q p = (Q2Qcb 1) /\ Qcbmult p q = (Q2Qcb 1)
      -> p != (Q2Qcb 0).
Proof.
  by move=> p q *; apply (@Qcb_intro_unit p q); tauto.
Qed.

Lemma Qcb_inv_out : forall (p : Qcb), negb (p != (Q2Qcb 0)) -> Qcbinv p = p.
Proof.
  by move=> p H; rewrite negbK in H; rewrite (eqP H) /Qcbinv /= /Qinv.
Qed.

(* FIXME strub: cannot do 1/x when defining Qcb_unitRingType as:

   Canonical Structure Qcb_unitRingType :=
      Eval hnf in UnitRingType Qcb_comUitRingMixin. *)

Definition Qcb_unitRingMixin :=
  UnitRingMixin Qcb_mulVx Qcb_mulxV Qcb_intro_unit_nC Qcb_inv_out.

Definition Qcb_comUnitRingMixin :=
  ComUnitRingMixin Qcb_mulVx Qcb_intro_unit Qcb_inv_out.

Canonical Structure Qcb_unitRingType :=
   Eval hnf in UnitRingType Qcb Qcb_unitRingMixin.

Canonical Structure Qcb_comUnitRingType := [comUnitRingType of Qcb].

(* Q/== ==> field *)
Definition Qcb_fieldMixin : GRing.Field.mixin_of Qcb_comUnitRingType.
Proof. by []. Qed.

Definition Qcb_idomainMixin := FieldIdomainMixin Qcb_fieldMixin.

Canonical Structure Qcb_iddomainType :=
  Eval hnf in IdomainType Qcb Qcb_idomainMixin.

Canonical Structure Qcb_fieldType :=
  Eval hnf in FieldType Qcb Qcb_fieldMixin.

(*
Definition Qcb_leb  (x y : Q) :=
  (Zle_bool (Qnum x * QDen y) (Qnum y * QDen x))%Z.
Definition Qcb_ltb  (x y : Q) :=
  (Zlt_bool (Qnum x * QDen y) (Qnum y * QDen x))%Z.
*)
(*
Local Notation "x <<= y" := (Qcb_leb x y).
Local Notation "x <<! y" := (Qcb_ltb x y).
*)

(* Definition Qcbleb (x y : Qcb) := (Qle_bool x y). *)

(* Lemma QcblebP : forall (x y : Qcb), reflect (x <= y)%Q (Qcbleb x y). *)
(* Proof. by move=> x y; apply: (iffP idP); move/Qle_bool_iff. Qed. *)

(* Lemma Qcbleb_antisymb : @ssrbool.antisymmetric Qcb Qcbleb. *)
(* Proof.  *)
(* move=> x y; case/andP; move/QcblebP=> h1; move/QcblebP=> h2. *)
(* by apply/eqP; apply/Qcb_QeqP; apply: Qle_antisym. *)
(* Qed. *)

(* Lemma Qcbleb_transb : @ssrbool.transitive Qcb Qcbleb. *)
(* Proof.  *)
(* move=> x y z; move/QcblebP=> h1; move/QcblebP=> h2; apply/QcblebP.  *)
(* exact: Qle_trans h2. *)
(* Qed. *)

(* Lemma Qcbleb_totalb : @ssrbool.total Qcb Qcbleb. *)
(* Proof. *)
(* move=> x y; case e: (Qcbleb x y)=> //=. *)
(* by move/QcblebP: e; move/Qnot_le_lt; move/Qlt_le_weak; move/QcblebP->. *)
(* Qed. *)

(* Lemma Qcbleb_addr : forall z x y : Qcb,  *)
(*   Qcbleb x y -> Qcbleb (x + z) (y + z). *)
(* Proof.  *)
(* move=> [x Hx] [y Hy] [z Hz]; move/QcblebP => Hxy; apply/QcblebP. *)
(* rewrite !qcb_valE in Hxy *. *)
(* setoid_rewrite Qred_correct. *)
(* by apply Qplus_le_compat; last apply Qle_refl . *)
(* Qed. *)

(* Lemma Qle_bool_mulr : forall x y,  *)
(*   Qle_bool 0 x -> Qle_bool 0 y -> Qle_bool 0 (x * y). *)
(* Proof.  *)
(* move=> x y; move/Zle_is_le_bool; rewrite Zmult_1_r=> px. *)
(* move/Zle_is_le_bool; rewrite Zmult_1_r => py. *)
(* by apply/Zle_is_le_bool; rewrite Zmult_1_r; apply: Zmult_le_0_compat. *)
(* Qed. *)

(* Lemma Qcbleb_mulr : forall x y, Qcbleb 0 x -> Qcbleb 0 y -> Qcbleb 0 (x * y). *)
(* Proof. *)
(*   move=> x y; move/QcblebP; rewrite qcb_valE; setoid_rewrite Qred_correct=> hx. *)
(*   move/QcblebP; rewrite qcb_valE; setoid_rewrite Qred_correct=> hy. *)
(*   apply/QcblebP; rewrite !qcb_valE; setoid_rewrite Qred_correct. *)
(*   exact: Qmult_le_0_compat. *)
(* Qed. *)

(* Definition Q_OrderedRingMixin :=  *)
(*   OrderedRing.Mixin  *)
(*   Qcbleb_antisymb Qcbleb_transb Qcbleb_totalb Qcbleb_addr Qcbleb_mulr. *)

(* Canonical Structure Qcb_oIddomainType := *)
(*   Eval hnf in OIdomainType Qcb Q_OrderedRingMixin. *)

(* Canonical Structure Qcb_oFieldType := *)
(*   Eval hnf in OFieldType Qcb Q_OrderedRingMixin. *)

Coercion Qcb_of_Z z := Q2Qcb (Qmake z xH).


(* Computable ring structure *)
Implicit Types x y : Qcb.

Definition qid : Qcb -> Qcb := @id Qcb.

Definition Q_czMixin := id_Mixins.id_czMixin [zmodType of Qcb].

Canonical Structure Q_czType :=
  Eval hnf in CZmodType Qcb Qcb Q_czMixin.

Lemma Q1 : qid 1 = 1.
Proof. by []. Qed.

Lemma qmulP : {morph qid : x y / x * y >-> x * y}.
Proof. by []. Qed.

Definition Q_cringMixin := @CRingMixin [ringType of Qcb] [czmodType Qcb of Qcb]
  1 (fun x y => x * y) Q1 qmulP.

Canonical Structure Q_cringType :=
  Eval hnf in CRingType [ringType of Qcb] Q_cringMixin.

Lemma unitQ : forall x, Qcb_unit x = Qcb_unit (qid x).
Proof. by []. Qed.

Lemma invQ : {morph qid : x / Qcbinv x >-> Qcbinv x}.
Proof. by []. Qed.

Definition Q_cunitRingMixin := @CUnitRingMixin [unitRingType of Qcb] [cringType Qcb of Qcb]
  Qcb_unit Qcbinv unitQ invQ.

Canonical Structure Q_cunitRingType :=
  Eval hnf in CUnitRingType [unitRingType of Qcb] Q_cunitRingMixin.

(* Divisibility theory for Q *)
Section Qdiv.

Definition odiv (a b : Qcb) :=
  if a == 0 then Some 0 else if b == 0 then None else Some (b^-1 * a).

Lemma odivQ : forall a b, DvdRing.div_spec a b (odiv a b).
Proof.
rewrite /odiv => a b.
case: ifP => a0.
  constructor.
  by rewrite (eqP a0) mul0r.
case: ifP=> b0; constructor.
  move=> x.
  apply/negP.
  by rewrite (eqP b0) mulr0 a0.
rewrite -mulrA mulrCA mulVr.
  by rewrite mulr1.
by rewrite unitfE b0.
Qed.

Definition QDvd := DvdRingMixin odivQ.
Canonical Structure QDvdRingType := DvdRingType Qcb QDvd.

(* GcdRing structure *)
Definition gcd (a b : Qcb) : Qcb := if (a == 0) && (b == 0) then 0 else 1.

Lemma gcdQ : forall a b g, g %| gcd a b = (g %| a) && (g %| b).
Proof.
move => a b /= g.
rewrite /gcd.
case: ifP => a0.
  by case/andP: a0 => /eqP -> /eqP ->.
apply/idP/andP.
  case/dvdrP=> x hx.
  split.
    apply/dvdrP.
    exists (a * x).
    by rewrite -mulrA -hx mulr1.
  apply/dvdrP.
  exists (b * x).
  by rewrite -mulrA -hx mulr1.
case.
case/nandP: a0; rewrite -unitfE dvdr1.
  move=> ua.
  by rewrite dvdrU // -unitd1.
move=> ub _.
by rewrite dvdrU // -unitd1.
Qed.

Definition QGcd := GcdRingMixin gcdQ.
Canonical Structure QgcdRingType := GcdRingType Qcb QGcd.

(* BezoutRing structure *)
Definition bezout (a b : Qcb) :=
  if a != 0 then (a^-1,0) else if b != 0 then (0,b^-1) else (0,0).

Lemma bezoutQ : forall a b, BezoutRing.bezout_spec a b (bezout a b).
Proof.
move=> a b.
rewrite /bezout.
case: ifP => [a0 | /eqP ->].
  by constructor; rewrite mul0r addr0 /gcdr /= /gcd (negbTE a0) mulVr.
case: ifP => [b0 |/eqP -> //].
by constructor; rewrite mul0r add0r /gcdr /= /gcd (negbTE b0) andbF mulVr.
Qed.

Definition QBezout := BezoutRingMixin bezoutQ.
Canonical Structure QbezoutRingType := BezoutRingType Qcb QBezout.

(* Computable dvdring structure *)
Lemma QCDvd : forall (x y : Qcb), omap qid (x %/? y) = ((qid x) %/? (qid y)).
Proof.
rewrite /qid => x y.
by case: (x %/? y).
Qed.

Definition Q_cdvdRingMixin := CDvdRingMixin QCDvd.

Canonical Structure Q_cdvdRingType :=
  Eval hnf in CDvdRingType [dvdRingType of Qcb] Q_cdvdRingMixin.

(* Computable gcdring structure *)
Lemma QCGcd : {morph qid : x y / gcdr x y >-> gcdr x y}.
Proof. by []. Qed.

Definition Q_cgcdRingMixin := CGcdRingMixin QCGcd.

Canonical Structure Q_cgcdRingType :=
  Eval hnf in CGcdRingType [gcdRingType of Qcb] Q_cgcdRingMixin.

(* Computable bezout structure *)
Lemma QCBezout : forall x y, (qid (bezout x y).1,qid (bezout x y).2) =
                             bezout (qid x) (qid y).
Proof. by move=> x y; case: (bezout x y). Qed.

Definition Q_cbezoutRingMixin := CBezoutRingMixin QCBezout.

Canonical Structure Q_cbezoutRingType :=
  Eval hnf in CBezoutRingType [bezoutRingType of Qcb] Q_cbezoutRingMixin.

End Qdiv.