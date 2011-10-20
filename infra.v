Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import choice fintype finfun ssrfun bigop ssralg.
(* Require Import orderedalg. *)

Require Import Zbool.
Require Import QArith.
Require Import Qcanon.

Close Scope Q_scope.

Set   Implicit Arguments.
Unset Strict Implicit.

Import Prenex Implicits.

Import GRing.

Open Local Scope ring_scope.

(* -------------------------------------------------------------------- *)
(* Various eqtype, subtype, choice, count canonical structures          *)
(*               from the standard library                              *)
(* -------------------------------------------------------------------- *)

(* Structures on positive *)

Definition eqp (p q : positive) : bool :=
  match ((p ?= q) Eq)%positive with Eq => true | _ => false end.

Lemma eqpP : Equality.axiom eqp.
Proof.
  move=> p q; apply: (iffP  idP)=>[|<-]; last by rewrite /eqp Pcompare_refl.
  rewrite /eqp; case e: ((p ?= q) Eq)%positive=> // _; exact: Pcompare_Eq_eq.
Qed.

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
Proof. by exact Zplus_assoc. Qed.

Lemma ZplusC : commutative Zplus.
Proof. by exact Zplus_comm. Qed.

Lemma Zplus0 : left_id (0%Z) Zplus.
Proof. by exact Zplus_0_l. Qed.

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
Proof.
move=> x y; rewrite mulrC -[y * x]/(Zmult y x); move/Zmult_1_inversion_l.
by case=> ->.
Qed.

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

