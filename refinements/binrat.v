(** * A refinement of Mathcomp's rationals [rat] with [bigQ] from Coq standard library. *)

Require Import ZArith QArith.
From Bignums Require Import BigQ.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat order.
From mathcomp Require Import ssralg ssrnum ssrint rat div.
From CoqEAL.refinements Require Import hrel refinements param binint.
Import Refinements.Op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope Z_scope.

Import GRing.Theory Order.Theory Num.Theory.

(** ** Link between [Z] (Coq standard lib) and [int] (Mathcomp) *)
Section Zint.

(** *** Various lemmas about [nat_of_pos] *)

Lemma nat_of_pos_inj x y : nat_of_pos x = nat_of_pos y -> x = y.
Proof. rewrite -!binnat.to_natE; apply Pos2Nat.inj. Qed.

Lemma nat_of_pos_gt0 p : (0 < nat_of_pos p)%N.
Proof. by elim: p =>//= p IHp; rewrite NatTrec.doubleE double_gt0. Qed.

Lemma Posz_nat_of_pos_neq0 p : Posz (nat_of_pos p) == 0%R = false.
Proof.
rewrite -binnat.to_natE.
case E: (Pos.to_nat _)=>//; exfalso; move: E.
by move: (binnat.to_nat_gt0 p); case (Pos.to_nat _).
Qed.

(** *** Conversion from [Z] to [int] *)
Definition Z2int (z : BinNums.Z) :=
  match z with
  | Z0 => 0%:Z
  | Z.pos p => (nat_of_pos p)%:Z
  | Z.neg n => (- (nat_of_pos n)%:Z)%R
  end.

(** *** Conversion from [int] to [Z] *)
Definition int2Z (n : int) : BinNums.Z :=
  match n with
  | Posz O => Z0
  | Posz n => Z.pos (Pos.of_nat n)
  | Negz n => Z.neg (Pos.of_nat n.+1)
  end.

Lemma Z2int_inj x y : Z2int x = Z2int y -> x = y.
Proof.
rewrite /Z2int.
case x, y=>//.
{ move=>[] H.
  by rewrite -[Z0]/(Z.of_nat 0%N) H -binnat.to_natE positive_nat_Z. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat _)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
{ rewrite -binnat.to_natE; case E: (Pos.to_nat _)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
{ by move=>[] /nat_of_pos_inj ->. }
{ rewrite -!binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case (Pos.to_nat p0)=>//=.
  by move=>[] H; move: (binnat.to_nat_gt0 p); rewrite H ltnn. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat _)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
{ rewrite -!binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat p)=>//=.
  by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
rewrite -!binnat.to_natE /GRing.opp /= /intZmod.oppz /=.
case E: (Pos.to_nat p)=>//=.
{ by move: (binnat.to_nat_gt0 p); rewrite -E ltnn. }
case E': (Pos.to_nat p0)=>//= [] [] H.
by move: E'; rewrite -H -E=>/Pos2Nat.inj ->.
Qed.

Lemma int2ZK : cancel int2Z Z2int.
Proof.
case => [n|n]; case: n => [|n] //=.
case: n => [//|n].
{ by rewrite -binnat.to_natE -Nat2Pos.inj_succ // Nat2Pos.id. }
case: n => [//|n].
{ by rewrite -binnat.to_natE -!Nat2Pos.inj_succ // Nat2Pos.id. }
Qed.

Lemma Z2intK : cancel Z2int int2Z.
Proof.
case => [|p|p] //=.
{ have Pp := nat_of_pos_gt0 p.
  by rewrite /= -(prednK Pp) (prednK Pp) -binnat.to_natE Pos2Nat.id. }
rewrite /int2Z.
have Pp := nat_of_pos_gt0 p.
rewrite -(prednK Pp) {Pp} /= -!binnat.to_natE.
rewrite -[in RHS](Pos2Nat.id p).
set n := Pos.to_nat p.
by case: n.
Qed.

(** *** [Z2int] is a morphism for arithmetic operations *)

Lemma Z2int_opp n : Z2int (- n) = (- (Z2int n))%R.
Proof. by case n=>// p /=; rewrite GRing.opprK. Qed.

Lemma Z2int_add x y : Z2int (x + y) = (Z2int x + Z2int y)%R.
Proof.
rewrite /Z2int /GRing.add /= /intZmod.addz /Z.add; case x, y=>//.
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz.
  by case (Pos.to_nat p)=>// n; rewrite subn0. }
{ by rewrite addn0. }
{ (try by rewrite nat_of_add_pos) || by rewrite nat_of_addn_gt0. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz.
  move: (Z.pos_sub_discr p p0); case (Z.pos_sub _ _).
  { move<-; rewrite -binnat.to_natE; case (Pos.to_nat _)=>// n.
    by rewrite ltnSn subnn. }
  { move=> p' ->; rewrite -!binnat.to_natE Pos2Nat.inj_add.
    case (Pos.to_nat p0); [by rewrite Nat.add_0_l addn0|move=> n].
    rewrite ifT; [by rewrite plusE addKn|].
    by rewrite plusE; apply ltn_addr; rewrite ltnSn. }
  move=> p' ->; rewrite -!binnat.to_natE Pos2Nat.inj_add.
  case (Pos.to_nat p').
  { rewrite Nat.add_0_r; case (Pos.to_nat p)=>// n.
    by rewrite ltnSn subnn. }
  move=> n.
  case E: (Pos.to_nat p)=>/=; [by rewrite subn0|].
  rewrite ifF.
  { by rewrite plusE addnS -addSn addKn. }
  by rewrite plusE addnS -addSn -ltn_subRL subnn ltn0. }
{ rewrite /GRing.opp /= /intZmod.oppz -binnat.to_natE.
  by case (Pos.to_nat p); [rewrite addn0|move=>n; rewrite subn0]. }
{ rewrite -binnat.to_natE /GRing.opp /= /intZmod.oppz.
  move: (Z.pos_sub_discr p p0); case E': (Z.pos_sub _ _).
  { move<-; rewrite -binnat.to_natE Z.pos_sub_diag; case (Pos.to_nat _)=>// n.
    by rewrite ltnSn subnn. }
  { move=> ->.
    rewrite -!binnat.to_natE Pos2Nat.inj_add Z.pos_sub_lt; last first.
    { by apply Pos.lt_add_diag_r. }
    rewrite -binnat.to_natE Pos2Nat.inj_sub ?Pos2Nat.inj_add; last first.
    { by apply Pos.lt_add_diag_r. }
    rewrite plusE minusE addKn; case (Pos.to_nat _).
    { by rewrite addn0; case (Pos.to_nat p0)=>// n; rewrite ltnSn subnn. }
    move=> n.
    case E: (Pos.to_nat p0 + n.+1)%N.
    { by exfalso; move: E; rewrite addnS. }
    rewrite -E ifF.
    { f_equal.
      have H: (Pos.to_nat p0 + n.+1 - n.+1 = Pos.to_nat p0 + n.+1 - n.+1)%N.
      { done. }
      move: H; rewrite {2}E addnK=>->.
      by rewrite subnS subSn /= ?subKn //; move: E;
        rewrite addnS=>[] [] <-; rewrite leq_addl. }
    by rewrite addnS -ltn_subRL subnn ltn0. }
  move=> ->; rewrite Z.pos_sub_gt; [|by apply Pos.lt_add_diag_r].
  rewrite -!binnat.to_natE !Pos2Nat.inj_sub; [|by apply Pos.lt_add_diag_r].
  rewrite Pos2Nat.inj_add; case (Pos.to_nat p).
  { by rewrite plusE minusE !add0n subn0. }
  by move=> n; rewrite plusE minusE addKn ifT // leq_addr. }
rewrite -!binnat.to_natE Pos2Nat.inj_add /GRing.opp /= /intZmod.oppz plusE.
case (Pos.to_nat p).
{ by rewrite add0n; case (Pos.to_nat p0)=>// n; rewrite ltn0 subn0. }
move=> n; case (Pos.to_nat p0); [by rewrite addn0 ltn0 subn0|].
by move=> n'; rewrite addSn -addnS.
Qed.

Lemma Z2int_mul_nat_of_pos (x : BinNums.Z) (y : positive) :
  (Z2int x * nat_of_pos y)%R = Z2int (Z.mul x (BinNums.Zpos y)).
Proof.
rewrite /Z2int; case Ex: x.
{ by rewrite mul0r Z.mul_0_l. }
{ by rewrite /= -!binnat.to_natE Pos2Nat.inj_mul. }
by rewrite /= mulNr  -!binnat.to_natE Pos2Nat.inj_mul.
Qed.

Lemma Z2int_mul x y : Z2int (x * y) = (Z2int x * Z2int y)%R.
Proof.
case y=>/=.
{ by rewrite GRing.mulr0 Z.mul_0_r. }
{ by move=> p; rewrite Z2int_mul_nat_of_pos. }
move=> p.
by rewrite GRing.mulrN Z2int_mul_nat_of_pos -Z2int_opp Zopp_mult_distr_r.
Qed.

Lemma Z2int_le x y : (Z2int x <= Z2int y)%R <-> Z.le x y.
Proof.
rewrite /Z2int; case Ex: x; case Ey: y=> //.
{ rewrite oppr_ge0; split; move=> H; exfalso; move: H; [|by rewrite /Z.le].
  apply/negP; rewrite -ltNge; apply nat_of_pos_gt0. }
{ split; move=> H; exfalso; move: H; [|by rewrite /Z.le].
  apply/negP; rewrite -ltNge; apply nat_of_pos_gt0. }
{ rewrite -!binnat.to_natE /Num.Def.ler /=.
  by rewrite -!positive_nat_Z -Nat2Z.inj_le; split => /ssrnat.leP. }
{ split; move=> H; exfalso; move: H; [|by rewrite /Z.le].
  apply /negP; rewrite -ltNge.
  by apply: (@lt_trans _ _ 0%R); rewrite ?oppr_lt0; apply nat_of_pos_gt0. }
{ rewrite oppr_le0; split; by rewrite /Z.le. }
{ split=>_; [by rewrite /Z.le|].
  by apply: (@le_trans _ _ 0%R); [apply oppr_le0|apply ltW, nat_of_pos_gt0]. }
rewrite ler_opp2; split.
{ rewrite /Z.le /Z.compare -!binnat.to_natE /Num.Def.ler /= => /ssrnat.leP.
  by rewrite -Pos.compare_antisym -Pos2Nat.inj_le -Pos.compare_le_iff. }
rewrite /Z.le /Z.compare -!binnat.to_natE /Num.Def.ler /=.
rewrite -Pos.compare_antisym => H; apply/ssrnat.leP.
by rewrite -Pos2Nat.inj_le -Pos.compare_le_iff.
Qed.

Lemma Z2int_lt x y : (Z2int x < Z2int y)%R <-> Z.lt x y.
Proof.
rewrite -lez_addr1 -[1%R]/(Z2int 1) -Z2int_add Z2int_le; omega.
Qed.

Lemma nat_of_pos_Z_to_pos x : nat_of_pos x = `|Z2int (Z.pos x)|%N.
Proof. by rewrite /absz /Z2int. Qed.

Lemma Zabs_natE n : Z.abs_nat n = `|Z2int n|%N.
Proof.
case: n => //= p; first by rewrite binnat.to_natE.
by rewrite abszN absz_nat binnat.to_natE.
Qed.

(** *** Various lemmas about gcd *)

Lemma dvdnP m n : reflect (Z.divide (Z.of_nat m) (Z.of_nat n)) (m %| n).
Proof.
apply: (iffP idP) => H.
{ rewrite dvdn_eq in H; rewrite -(eqP H) /Z.divide; exists (Z.of_nat (n %/ m)).
  by rewrite Nat2Z.inj_mul. }
{ have [q Hq] := H; apply/dvdnP; exists `|Z2int q|%N; apply/Nat2Z.inj.
  have [Zq|NZq] := Z_zerop q.
  { by rewrite Zq /= in Hq *. }
  case: m Hq H => [|m] Hq H.
  { by rewrite Zmult_comm /= in Hq; rewrite mulnC /=. }
  rewrite Nat2Z.inj_mul -Zabs_natE Zabs2Nat.id_abs Z.abs_eq //.
  have H0 : (0 <= q * Z.of_nat m.+1) by rewrite -Hq; apply Zle_0_nat.
  by apply: Zmult_le_0_reg_r H0. }
Qed.

Lemma ZgcdE n d : Z.gcd n (Z.pos d) = Z.of_nat (div.gcdn `|Z2int n| (nat_of_pos d)).
Proof.
apply: Z.gcd_unique.
{ exact: Zle_0_nat. }
{ apply/Z.divide_abs_r; rewrite -Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE dvdn_gcdl. }
{ apply/Z.divide_abs_r; rewrite -Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE /= dvdn_gcdr. }
move=> q Hn Hd; apply/Z.divide_abs_l; rewrite -Zabs2Nat.id_abs; apply/dvdnP.
rewrite Zabs_natE dvdn_gcd.
apply/andP; split; apply/dvdnP; rewrite -!Zabs_natE !Zabs2Nat.id_abs.
{ by apply/Z.divide_abs_l/Z.divide_abs_r. }
{ by apply/Z.divide_abs_l; rewrite -binnat.to_natE positive_nat_Z. }
Qed.

Lemma ZgcdE' n m : Z.gcd n m = Z.of_nat (gcdn `|Z2int n| `|Z2int m|).
Proof.
case m.
{ rewrite Z.gcd_0_r {2}/absz {2}/Z2int /= gcdn0 -Zabs2Nat.id_abs; f_equal.
  rewrite /Z.abs_nat /absz /Z2int.
  case n=>// p; rewrite -!binnat.to_natE //.
  case (Pos.to_nat _); [by rewrite GRing.oppr0|move=> n'].
  by rewrite /GRing.opp /=. }
{ by move=> p; rewrite ZgcdE nat_of_pos_Z_to_pos. }
by move=> p; rewrite -Z.gcd_opp_r /= ZgcdE abszN /absz.
Qed.

Lemma Z_ggcd_1_r n : Z.ggcd n 1 = (1, (n, 1))%Z.
Proof.
move: (Z.ggcd_gcd n 1) (Z.ggcd_correct_divisors n 1); rewrite Z.gcd_1_r.
case (Z.ggcd _ _)=> g ab /= ->; case ab=> a b [].
by rewrite !Z.mul_1_l => <- <-.
Qed.

Lemma Z_ggcd_coprime a b :
  let '(g, (a', b')) := Z.ggcd a b in
  g <> 0%Z -> coprime `|Z2int a'| `|Z2int b'|.
Proof.
move: (Z.ggcd_gcd a b) (Z.ggcd_correct_divisors a b).
case (Z.ggcd _ _)=> g ab; case ab=> a' b' /= Hg [] Ha Hb Pg.
rewrite /coprime; apply/eqP /Nat2Z.inj; rewrite -ZgcdE' /=.
suff ->: a' = (a / g)%Z.
{ suff ->: b' = (b / g)%Z; [by apply Z.gcd_div_gcd|].
  by rewrite Hb Z.mul_comm Z_div_mult_full. }
by rewrite Ha Z.mul_comm Z_div_mult_full.
Qed.

End Zint.

(** ** Link between [bigQ] (Coq standard lib) and [rat] (Mathcomp) *)
Section binrat_theory.

Arguments refines A%type B%type R%rel _ _. (* Fix a scope issue with refines *)

(** *** Conversion from [bigQ] to [rat] *)
Program Definition bigQ2rat (bq : bigQ) :=
  let q := Qred [bq]%bigQ in
  @Rat (Z2int (Qnum q), Z2int (Z.pos (Qden q))) _.
Next Obligation.
rewrite ltz_nat nat_of_pos_gt0 /=.
set q := [bq]%bigQ.
have /Qcanon.Qred_iff HQ := Qcanon.Qred_involutive q.
set n := Qnum (Qred q) in HQ *.
set d := Qden (Qred q) in HQ *.
rewrite ZgcdE in HQ.
by rewrite /div.coprime; apply/eqP/Nat2Z.inj; rewrite HQ.
Qed.

(** *** Conversion from [rat] to [bigQ] *)
Definition rat2bigQ (q : rat) : bigQ :=
  let n := BigZ.of_Z (int2Z (numq q)) in
  let d := BigN.N_of_Z (int2Z (denq q)) in
  (n # d)%bigQ.

(** *** Refinement relation *)
Definition r_ratBigQ := fun_hrel bigQ2rat.

(** *** Main instances *)

Global Instance zero_bigQ : zero_of bigQ := 0%bigQ.
Global Instance one_bigQ : one_of bigQ := 1%bigQ.
Global Instance opp_bigQ : opp_of bigQ := BigQ.opp.
Global Instance add_bigQ : add_of bigQ := BigQ.add.
Global Instance sub_bigQ : sub_of bigQ := BigQ.sub.
Global Instance mul_bigQ : mul_of bigQ := BigQ.mul.
Global Instance eq_bigQ : eq_of bigQ := BigQ.eq_bool.
Global Instance lt_bigQ : lt_of bigQ := fun p q => if BigQ.compare p q is Lt then true else false.
Global Instance le_bigQ : leq_of bigQ := fun p q => if BigQ.compare q p is Lt then false else true.

(** *** Proofs of refinement *)

Global Instance refine_ratBigQ_zero : refines r_ratBigQ 0%R 0%C.
Proof. rewrite refinesE /r_ratBigQ /bigQ2rat; red; exact: val_inj. Qed.

Global Instance refine_ratBigQ_one : refines r_ratBigQ 1%R 1%C.
Proof. rewrite refinesE /r_ratBigQ /bigQ2rat; red; exact: val_inj. Qed.

Global Instance refine_ratBigQ_opp : refines (r_ratBigQ ==> r_ratBigQ) -%R -%C.
Proof.
apply refines_abstr=> a b.
rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rab.
rewrite /GRing.opp /= /oppq /opp_op /opp_bigQ /BigQ.opp.
move: rab; case b.
{ move=> n <-; rewrite /GRing.opp /=; apply val_inj=>/=.
  rewrite !Z_ggcd_1_r /= gcdn1 !divn1 BigZ.spec_opp Z2int_opp.
  by rewrite expN1r mulz_sign_abs. }
rewrite -oppq_frac.
move=> n d <-; apply val_inj=>/=.
set n' := Qnum _.
set d' := Qden _.
set n'' := Qnum _.
set d'' := Qden _.
set g := gcdn _ _.
have Hg: g = 1%N; [|rewrite Hg divn1].
{ apply Nat2Z.inj; rewrite /g -ZgcdE /=.
  apply Qcanon.Qred_iff, Qcanon.Qred_involutive. }
rewrite !Posz_nat_of_pos_neq0 divn1 expN1r mulz_sign_abs abszN -/g Hg !divn1.
rewrite !absz_nat.
have ->: (Posz (nat_of_pos d'') < 0)%R = false by [].
rewrite /= -(abszN (Z2int n'')) mulz_sign_abs; f_equal.
{ rewrite -Z2int_opp; f_equal.
  rewrite /n' /n''; case (_ =? _)%bigN=>//.
  rewrite BigZ.spec_opp /= Z.ggcd_opp /=.
  by case (Z.ggcd _)=> ? p; case p. }
rewrite /d' /d''; case (_ =? _)%bigN=>//=.
rewrite BigZ.spec_opp /= Z.ggcd_opp /=.
by case (Z.ggcd _)=> ? p; case p.
Qed.

Global Instance refine_ratBigQ_add :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) +%R +%C.
Proof.
apply refines_abstr2=> a b rab c d rcd.
rewrite /GRing.add /= /addq /add_op /add_bigQ.
case Ea: ((valq a).2 == 0%R).
{ exfalso; move: rab Ea; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=><-/=;
  by rewrite Posz_nat_of_pos_neq0. }
case Ec: ((valq c).2 == 0%R).
{ exfalso; move: rcd Ec; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=><-/=;
  by rewrite Posz_nat_of_pos_neq0. }
rewrite -addq_frac ?Ea ?Ec // !valqK.
rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel; apply val_inj=>/=.
have ->: Qred [b + d]%bigQ = Qred (Qred [b]%bigQ + Qred [d]%bigQ).
{ by apply Qred_complete; rewrite BigQ.spec_add !Qred_correct. }
move: rab rcd.
rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=><-<-/=.
set nb := Qnum (Qred _).
set db := Qden (Qred _).
set nd := Qnum (Qred _).
set dd := Qden (Qred _).
rewrite /GRing.add /GRing.mul /=.
rewrite -!binnat.to_natE -multE -Pos2Nat.inj_mul !binnat.to_natE.
rewrite Posz_nat_of_pos_neq0.
case E: ((Z.ggcd _ _).2)=>/=; move: E.
rewrite (surjective_pairing (_.2))=>[] [] <- <-.
set nr := (Z.add _ _).
set dr := (BinNums.Zpos _).
move: (Z.ggcd_gcd nr dr) (Z.ggcd_correct_divisors nr dr) (Z_ggcd_coprime nr dr).
case (Z.ggcd _ _)=>g ab /= Hg; case ab=> a' b' [] /= Ha' Hb' CPab'.
rewrite -[intRing.mulz (Z2int nb) _]/(Z2int nb * nat_of_pos db)%R.
rewrite -[intRing.mulz (Z2int nd) _]/(Z2int nd * nat_of_pos dd)%R.
rewrite -[intZmod.addz _ _]/(Z2int nb * nat_of_pos db + Z2int nd * nat_of_pos dd)%R.
rewrite !Z2int_mul_nat_of_pos -Z2int_add -/nr !nat_of_pos_Z_to_pos -/dr.
rewrite Ha' Hb' !Z2int_mul !abszM.
have Pg' : (0 < Z2int g)%R.
{ rewrite Hg; case E: (Z.gcd _ _).
  { by exfalso; move: E; rewrite /Z.gcd; case nr. }
  { by rewrite /Z2int /Num.Def.ltr /GRing.zero /= nat_of_pos_gt0. }
  by exfalso; move: E; rewrite /Z.gcd; case nr. }
have Pg : (0 < `|Z2int g|)%N.
{ rewrite absz_gt0; apply/eqP=>H; move: Pg'; rewrite H.
  by rewrite /GRing.zero /Num.Def.ltr /= ltnn. }
rewrite -muln_gcdr !divnMl //.
have ->: gcdn `|Z2int a'| `|Z2int b'| = 1%N; [|rewrite !divn1].
{ by move: CPab'; rewrite /coprime=>H; apply/eqP/H=>{H}H; move: Pg'; rewrite H. }
suff ->: (Z2int g * Z2int a' < 0 = (Z2int a' < 0))%R.
{ rewrite -[_ (_ ^ _)%R _]/((-1) ^ (Z2int a' < 0)%R * Posz `|Z2int a'|%N)%R.
  rewrite expN1r mulz_sign_abs /Z.to_pos.
  move: Hb'; case b'=>//.
  { by rewrite Z.mul_0_r=>[]. }
  move=> p; move: Pg'; case g=>// p'.
  by rewrite /Z2int=>/= H; exfalso; move: H; rewrite oppr_gt0. }
by apply pmulr_rlt0.
Qed.

Global Instance refine_ratBigQ_sub :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) (fun x y => x - y)%R sub_op.
Proof.
apply refines_abstr2=> a b rab c d rcd.
rewrite /sub_op /sub_bigQ /BigQ.sub; eapply refines_apply; tc.
Qed.

Global Instance refine_ratBigQ_mul :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) *%R *%C.
Proof.
apply refines_abstr2=> a b rab c d rcd.
rewrite /GRing.mul /= /mulq -mulq_frac !valqK /mul_op /mul_bigQ.
rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel; apply val_inj=>/=.
have ->: Qred [b * d]%bigQ = Qred (Qred [b]%bigQ * Qred [d]%bigQ).
{ by apply Qred_complete; rewrite BigQ.spec_mul !Qred_correct. }
move: rab rcd.
rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=><-<-/=.
set nb := Qnum (Qred _).
set db := Qden (Qred _).
set nd := Qnum (Qred _).
set dd := Qden (Qred _).
rewrite /GRing.mul /= -!binnat.to_natE -multE -Pos2Nat.inj_mul !binnat.to_natE.
rewrite Posz_nat_of_pos_neq0.
case E: ((Z.ggcd _ _).2)=>/=; move: E.
rewrite (surjective_pairing (_.2))=>[] [] <- <-.
move: (Z_ggcd_coprime (nb * nd) (Z.pos (db * dd))).
move: (Z.ggcd_correct_divisors (nb * nd) (Z.pos (db * dd))).
move: (Z.ggcd_gcd (nb * nd) (Z.pos (db * dd))).
case (Z.ggcd _ _)=>g ab /= Hg; case ab=> a' b' [] /= Ha' Hb' CPab'.
have ->: intRing.mulz (Z2int nb) (Z2int nd) = Z2int (nb * nd).
{ by rewrite Z2int_mul. }
rewrite Ha' !nat_of_pos_Z_to_pos Hb' !Z2int_mul !abszM.
have Pg' : (0 < Z2int g)%R.
{ rewrite Hg; case E: (Z.gcd _ _).
  { by exfalso; move: E; rewrite /Z.gcd; case (Z.mul _ _). }
  { by rewrite /Z2int /Num.Def.ltr /GRing.zero /= nat_of_pos_gt0. }
  by exfalso; move: E; rewrite /Z.gcd; case (Z.mul _ _). }
have Pg : (0 < `|Z2int g|)%N.
{ rewrite absz_gt0; apply/eqP=>H; move: Pg'; rewrite H.
  by rewrite /GRing.zero /Num.Def.ltr /= ltnn. }
rewrite -muln_gcdr !divnMl //.
have ->: gcdn `|Z2int a'| `|Z2int b'| = 1%N; [|rewrite !divn1].
{ by move: CPab'; rewrite /coprime=>H; apply/eqP/H=>{H}H; move: Pg'; rewrite H. }
suff ->: (Z2int g * Z2int a' < 0 = (Z2int a' < 0))%R.
{ rewrite -[_ (_ ^ _)%R _]/((-1) ^ (Z2int a' < 0)%R * Posz `|Z2int a'|%N)%R.
  rewrite expN1r mulz_sign_abs /Z.to_pos.
  move: Hb'; case b'=>//.
  { by rewrite Z.mul_0_r=>[]. }
  move=> p; move: Pg'; case g=>// p'.
  by rewrite /Z2int=>/= H; exfalso; move: H; rewrite oppr_gt0. }
by apply pmulr_rlt0.
Qed.

Global Instance refine_ratBigQ_eq :
  refines (r_ratBigQ ==> r_ratBigQ ==> eq) eqtype.eq_op eq_op.
Proof.
apply refines_abstr2=> a b rab c d rcd.
rewrite /eq_op /eq_bigQ /BigQ.eq_bool.
case E: (_ == _); case E': (_ ?= _)%bigQ=>//; rewrite ?refinesE //; exfalso.
{ move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
  move: E; rewrite -rba -rdc=> /eqP [] /Z2int_inj Hn /nat_of_pos_inj Hd.
  move: E'; rewrite BigQ.spec_compare Qred_compare -Qlt_alt /Qlt Hn Hd.
  apply Z.lt_irrefl. }
{ move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
  move: E; rewrite -rba -rdc=> /eqP [] /Z2int_inj Hn /nat_of_pos_inj Hd.
  move: E'; rewrite BigQ.spec_compare Qred_compare -Qgt_alt /Qlt Hn Hd.
  apply Z.lt_irrefl. }
move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
move: E; rewrite -rba -rdc=> /eqP H; apply H, val_inj=>/={H}.
by move: E'; rewrite BigQ.spec_compare -Qeq_alt=>/Qred_complete ->.
Qed.

Global Instance refine_ratBigQ_lt :
  refines (r_ratBigQ ==> r_ratBigQ ==> bool_R) Num.lt lt_op.
Proof.
apply refines_abstr2=> a b rab c d rcd.
rewrite /lt_op /lt_bigQ.
case E: (_ < _)%R; case E': (_ ?= _)%bigQ; rewrite refinesE //; exfalso.
{ move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
  move: E; rewrite -rba -rdc.
  rewrite /Num.Def.ltr /= /lt_rat /numq /denq /=.
  move: E'; rewrite BigQ.spec_compare Qred_compare -Qeq_alt /Qeq.
  by rewrite !Z2int_mul_nat_of_pos=>->; rewrite ltxx. }
{ move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
  move: E; rewrite -rba -rdc.
  rewrite /Num.Def.ltr /= /lt_rat /numq /denq /=.
  move: E'; rewrite BigQ.spec_compare Qred_compare -Qgt_alt /Qlt.
  rewrite !Z2int_mul_nat_of_pos=>H; move/Z2int_lt.
  by apply Zle_not_lt, Z.lt_le_incl. }
move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
move: E; rewrite -rba -rdc.
rewrite /Num.Def.ltr /= /lt_rat /numq /denq /=.
move: E'; rewrite BigQ.spec_compare Qred_compare -Qlt_alt /Qlt.
rewrite !Z2int_mul_nat_of_pos=>H.
by move/negP /Z2int_lt=>H'; apply H'.
Qed.

Global Instance refine_ratBigQ_le :
  refines (r_ratBigQ ==> r_ratBigQ ==> bool_R) Num.le leq_op.
Proof.
apply refines_abstr2=> a b rab c d rcd.
rewrite /leq_op /le_bigQ.
case E: (_ <= _)%R; case E': (_ ?= _)%bigQ; rewrite refinesE //; exfalso.
{ move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
  move: E; rewrite -rba -rdc.
  rewrite /Num.Def.ler /= /le_rat /numq /denq /=.
  move: E'; rewrite BigQ.spec_compare Qred_compare -Qlt_alt /Qlt.
  by rewrite !Z2int_mul_nat_of_pos=>H; move/Z2int_le; apply Zlt_not_le. }
{ move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
  move: E; rewrite -rba -rdc.
  rewrite /Num.Def.ler /= /le_rat /numq /denq /=.
  move: E'; rewrite BigQ.spec_compare Qred_compare -Qeq_alt /Qeq.
  by rewrite !Z2int_mul_nat_of_pos=>->; rewrite lexx. }
move: rab rcd; rewrite refinesE /r_ratBigQ /bigQ2rat /fun_hrel=> rba rdc.
move: E; rewrite -rba -rdc.
rewrite /Num.Def.ler /= /le_rat /numq /denq /=.
move: E'; rewrite BigQ.spec_compare Qred_compare -Qgt_alt /Qlt.
rewrite !Z2int_mul_nat_of_pos=>H.
by move/negP /Z2int_le=>H'; apply H', Z.lt_le_incl.
Qed.

End binrat_theory.
