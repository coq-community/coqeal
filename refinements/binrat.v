(** * A refinement of Mathcomp's rationals [rat] with [bigQ] from Coq standard library. *)

Require Import ZArith QArith Lia.
From Bignums Require Import BigQ.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat order.
From mathcomp Require Import ssralg ssrnum ssrint rat div intdiv.
From CoqEAL.refinements Require Import hrel refinements param binint.
Import Refinements.Op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope Z_scope.

Import GRing.Theory Order.Theory Num.Theory.

Section classes.

Class max_of C := max_op : C -> C -> C.
Class min_of C := min_op : C -> C -> C.

End classes.

(** ** Link between [Z] (Coq standard lib) and [int] (Mathcomp) *)
Section Zint.

(** *** Various lemmas about [nat_of_pos] *)

Lemma nat_of_pos_inj x y : nat_of_pos x = nat_of_pos y -> x = y.
Proof. rewrite -!binnat.to_natE; apply Pos2Nat.inj. Qed.

Lemma nat_of_pos_gt0 p : (0 < nat_of_pos p)%N.
Proof. by elim: p =>//= p IHp; rewrite NatTrec.doubleE double_gt0. Qed.

Lemma nat_of_pos_gtr0 p : (0 < Posz (nat_of_pos p))%R.
Proof. by rewrite -[0%R]/(Posz 0) ltz_nat nat_of_pos_gt0. Qed.

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

Lemma Z2int_abs x : Z2int (Z.abs x) = `|Z2int x|%nat.
Proof. by case: x => // p /=; rewrite abszN. Qed.

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

Lemma divE x y : Nat.div x y = divn x y.
Proof.
case: y => [//|y].
rewrite /Nat.div.
move: (Nat.divmod_spec x y 0 y).
case: Nat.divmod => q r /(_ (le_n _)) [].
rewrite Nat.mul_0_r Nat.sub_diag !Nat.add_0_r Nat.mul_comm => + Hr /=.
rewrite multE minusE plusE => /(f_equal (fun x => divn x y.+1)) ->.
rewrite divnMDl // divn_small ?addn0 //.
rewrite ltn_subLR; [|exact/ssrnat.leP].
  by rewrite -addSnnS addnC addnS ltnS leq_addr.
Qed.

(* Mathcomp's divz and Z.div don't match for negative values. *)
Lemma Z2int_div x y : Z.le 0 x -> Z.le 0 y ->
  Z2int (Z.div x y) = (Z2int x %/ Z2int y)%Z.
Proof.
case: x => [|x|//] _; [by rewrite intdiv.div0z|].
case: y => [|y|//] _; [by rewrite intdiv.divz0|].
rewrite -!positive_nat_Z -div_Zdiv; last first.
{ rewrite Nat.neq_0_lt_0; exact: Pos2Nat.is_pos. }
rewrite !positive_nat_Z /= /divz gtr0_sgz ?mul1r; last first.
{ exact: nat_of_pos_gt0. }
rewrite divE !binnat.to_natE absz_nat /Z2int.
move: (Zle_0_nat (nat_of_pos x %/ nat_of_pos y)).
rewrite -[X in _ = Posz X]Nat2Z.id.
  by case: Z.of_nat => //= p _; rewrite binnat.to_natE.
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
rewrite -lez_addr1 -[1%R]/(Z2int 1) -Z2int_add Z2int_le; lia.
Qed.

Lemma nat_of_pos_Z_to_pos x : nat_of_pos x = `|Z2int (Z.pos x)|%N.
Proof. by rewrite /absz /Z2int. Qed.

Lemma Zabs_natE n : Z.abs_nat n = `|Z2int n|%N.
Proof.
case: n => //= p; first by rewrite binnat.to_natE.
by rewrite abszN absz_nat binnat.to_natE.
Qed.

Lemma Z2int_Z_of_nat n : Z2int (Z.of_nat n) = n.
Proof.
by case: n => //= n; rewrite Pos.of_nat_succ -binnat.to_natE Nat2Pos.id.
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

Lemma Z2int_lcm x y : Z.le 0 x -> Z.le 0 y ->
  Z2int (Z.lcm x y) = lcmn `|Z2int x| `|Z2int y|.
Proof.
case: x => [|x|//] _; [by rewrite /= lcm0n|].
case: y => [|y|//] _; [by rewrite /= lcmn0|].
rewrite /Z.lcm Z2int_abs Z2int_mul Z2int_div //.
rewrite ZgcdE' abszM; apply: f_equal; apply/eqP.
rewrite -(@eqn_pmul2r (gcdn `|Z2int (Z.pos x)| `|Z2int (Z.pos y)|)); last first.
{ rewrite gcdn_gt0; apply/orP; left; rewrite absz_gt0 /= eqz_nat.
  apply: lt0n_neq0; exact: nat_of_pos_gt0. }
rewrite muln_lcm_gcd.
rewrite -(absz_nat (gcdn _ _)) -mulnA -abszM.
rewrite Z2int_Z_of_nat /=.
  by rewrite intdiv.divzK // /mem /in_mem /intdiv.dvdz /= dvdn_gcdr.
Qed.

End Zint.

(** ** Link between [bigQ] (Coq standard lib) and [rat] (Mathcomp) *)
Section binrat_theory.

Arguments refines A%type B%type R%rel _ _. (* Fix a scope issue with refines *)

(** *** Conversion from [bigQ] to [rat] *)
Program Definition bigQ2rat (bq : bigQ) :=
  let q := Qred [bq]%bigQ in
  ((Z2int (Qnum q))%:Q / (Z2int (Z.pos (Qden q)))%:Q)%R.

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
Global Instance add_bigQ : add_of bigQ := BigQ.add_norm.
Global Instance sub_bigQ : sub_of bigQ := BigQ.sub_norm.
Global Instance mul_bigQ : mul_of bigQ := BigQ.mul_norm.
Global Instance inv_bigQ : inv_of bigQ := BigQ.inv_norm.
Global Instance div_bigQ : div_of bigQ := BigQ.div_norm.
Global Instance eq_bigQ : eq_of bigQ := BigQ.eq_bool.
Global Instance lt_bigQ : lt_of bigQ := fun p q => if BigQ.compare p q is Lt then true else false.
Global Instance le_bigQ : leq_of bigQ := fun p q => if BigQ.compare q p is Lt then false else true.
Global Instance max_bigQ : max_of bigQ := BigQ.max.
Global Instance min_bigQ : min_of bigQ := BigQ.min.
Global Instance cast_of_nat_bigQ : cast_of nat bigQ := BigQ.of_Z \o Z.of_nat.
Global Instance spec_bigQ : spec_of bigQ rat := bigQ2rat.

(** *** Proofs of refinement *)

Global Instance refine_ratBigQ_zero : refines r_ratBigQ 0%R 0%C.
Proof. rewrite refinesE /r_ratBigQ /bigQ2rat; red; exact: val_inj. Qed.

Global Instance refine_ratBigQ_one : refines r_ratBigQ 1%R 1%C.
Proof. rewrite refinesE /r_ratBigQ /bigQ2rat; red; exact: val_inj. Qed.

Global Instance refine_ratBigQ_opp : refines (r_ratBigQ ==> r_ratBigQ) -%R -%C.
Proof.
rewrite refinesE => _ a <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel /=.
rewrite BigQ.strong_spec_opp Qred_opp [in LHS]/Qnum /=.
by rewrite Z2int_opp mulrNz mulNr.
Qed.

Lemma Z2int_Qred n d :
  ((Z2int (Qnum (Qred (n # d))))%:Q / (nat_of_pos (Qden (Qred (n # d))))%:Q
   = (Z2int n)%:Q / (Z2int (Z.pos d))%:Q)%R.
Proof.
rewrite -(fracqE (Z2int n, Z2int (Z.pos d))) -[RHS]divq_num_den.
rewrite /Qred.
move: (Z.ggcd_gcd n (Z.pos d)) (Z.ggcd_correct_divisors n (Z.pos d)).
move: (Z_ggcd_coprime n (Z.pos d)).
case: Z.ggcd => g [n' d'] /=.
case: g => [|g|g].
{ by move=> _ _ [_]; rewrite Z.mul_0_l. }
{ move=> coprime_n'_d' => _ [->].
  rewrite (nat_of_pos_Z_to_pos d) => /[dup] posd' ->.
  have d'n0 : `|Z2int d'| != 0%R.
  { rewrite normr_eq0.
    case: d' posd' {coprime_n'_d'} => // d' _.
    by rewrite Posz_nat_of_pos_neq0. }
  rewrite !Z2int_mul abszM PoszM gez0_abs; [|by rewrite -[0%R]int2ZK Z2int_le].
  rewrite fracqMM ?Posz_nat_of_pos_neq0 // abszE.
  move: (@valq_frac (Z2int n', `|Z2int d'|) d'n0).
  rewrite scalqE // mul1r => [[neq deq]].
  have -> : nat_of_pos (Z.to_pos d') = `|Z2int d'| :> int.
  { rewrite nat_of_pos_Z_to_pos Z2Pos.id ?abszE //.
    by case: d' posd' {coprime_n'_d' d'n0 neq deq}. }
  rewrite [X in (X%:~R / _)%R]neq [X in (_ / X%:~R)%R]deq.
  rewrite (_ : gcdn _ _ = 1%nat) ?mul1r //; exact/eqP/coprime_n'_d'. }
by move: (Z.gcd_nonneg n (Z.pos d)) => + _ => /[swap] <-.
Qed.

Lemma BigQ_red_den_nonzero q :
  match BigQ.red q with BigQ.Qz _ => True | BigQ.Qq _ d => [d]%bigN <> Z0 end.
Proof.
case: q => [//|n d] /=.
rewrite /BigQ.norm.
rewrite BigN.spec_compare.
case: Z.compare_spec => [| |//] Hgcd.
{ rewrite /BigQ.check_int BigN.spec_compare.
  case Z.compare_spec => [//| |//] Hd.
  apply: BigNumPrelude.Zlt0_not_eq.
  move: Hd; exact: Z.lt_trans. }
rewrite /BigQ.check_int BigN.spec_compare.
case Z.compare_spec => [//| |//] Hd.
apply: BigNumPrelude.Zlt0_not_eq.
move: Hd; exact: Z.lt_trans.
Qed.

Lemma r_ratBigQ_red x y : r_ratBigQ x y ->
  match BigQ.red y with
  | BigQ.Qz n => numq x = Z2int [n]%bigZ /\ denq x = 1%R
  | BigQ.Qq n d => numq x = Z2int [n]%bigZ /\ denq x = Z2int [d]%bigN
  end.
Proof.
case: (ratP x) => nx dx nx_dx_coprime {x}.
rewrite /r_ratBigQ /fun_hrel /bigQ2rat -BigQ.strong_spec_red.
have ry_red : Qred [BigQ.red y]%bigQ = [BigQ.red y]%bigQ.
{ by rewrite BigQ.strong_spec_red Qcanon.Qred_involutive. }
have ry_dneq0 := BigQ_red_den_nonzero y.
case: (BigQ.red y) ry_dneq0 ry_red => [ny _ _|ny dy dy_neq0].
{ rewrite /BigQ.to_Q /Qnum /Qden mulr1.
  move=> /(f_equal ( *%R^~ dx.+1%:~R)%R).
  rewrite mulfVK ?mulrz_neq0 // -intrM => /intr_inj nx_eq.
  have dx_1 : (dx.+1 = 1)%nat.
  { by move: nx_dx_coprime => /eqP <-; rewrite -nx_eq abszM /= gcdnC gcdnMl. }
    by rewrite -nx_eq dx_1 mulr1. }
rewrite /BigQ.to_Q ifF ?BigN.spec_eqb ?Z.eqb_neq //.
rewrite Qcanon.Qred_iff ZgcdE -[1%Z]/(Z.of_nat 1%nat) => /Nat2Z.inj.
rewrite /Qnum /Qden nat_of_pos_Z_to_pos => /eqP ny_dy_coprime.
move=> /eqP; rewrite rat_eqE !coprimeq_num // !coprimeq_den //=.
rewrite !gtr0_sg ?nat_of_pos_gtr0 // !mul1r => /andP[/eqP <-].
rewrite ifF; [|exact/eqP/eqP/lt0r_neq0/nat_of_pos_gtr0].
rewrite -!abszE !absz_nat => /eqP[<-]; split=> [//|].
rewrite -[LHS]/(Z2int (Z.pos (Z.to_pos [dy]%bigN))) Z2Pos.id //.
exact: BigQ.N_to_Z_pos.
Qed.

Global Instance refine_ratBigQ_add :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) +%R +%C.
Proof.
rewrite refinesE => _ a <- _ b <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel /=.
rewrite (Qred_complete _ _ (BigQ.spec_add_norm _ _)).
case: (BigQ.to_Q a) => na da {a}.
case: (BigQ.to_Q b) => nb db {b}.
rewrite /Qplus !Z2int_Qred.
rewrite Z2int_add !Z2int_mul /= nat_of_mul_pos.
rewrite intrD PoszM !intrM.
by rewrite [RHS]addf_div // intq_eq0 Posz_nat_of_pos_neq0.
Qed.

Global Instance refine_ratBigQ_sub :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) (fun x y => x - y)%R sub_op.
Proof.
apply refines_abstr2=> a b rab c d rcd.
rewrite /sub_op /sub_bigQ /BigQ.sub_norm; eapply refines_apply; tc.
Qed.

Global Instance refine_ratBigQ_mul :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ) *%R *%C.
Proof.
rewrite refinesE => _ a <- _ b <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel /=.
rewrite (Qred_complete _ _ (BigQ.spec_mul_norm _ _)).
case: (BigQ.to_Q a) => na da {a}.
case: (BigQ.to_Q b) => nb db {b}.
rewrite /Qmult !Z2int_Qred /=.
rewrite Z2int_mul nat_of_mul_pos.
rewrite PoszM !intrM.
by rewrite [RHS]mulf_div.
Qed.

Global Instance refine_ratBigQ_inv :
  refines (r_ratBigQ ==> r_ratBigQ)%rel GRing.inv inv_op.
Proof.
rewrite refinesE => _ a <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel /=.
rewrite (Qred_complete _ _ (BigQ.spec_inv_norm _)).
case: (BigQ.to_Q a) => na da {a}.
rewrite /Qinv [Qnum (na # da)]/=.
case: na => [|na|na].
{ by rewrite /= !mul0r invr0. }
{ by rewrite [Qden (_ # da)]/= !Z2int_Qred invf_div. }
rewrite [Qden (_ #da)]/= !Z2int_Qred invf_div.
by rewrite -!Pos2Z.opp_pos !Z2int_opp !mulrNz mulNr invrN mulrN.
Qed.

Global Instance refine_ratBigQ_div :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ)%rel (fun x y => x / y)%R div_op.
Proof.
apply: refines_abstr2 => x1 x2 rx y1 y2 ry.
rewrite /div_op /div_bigQ /BigQ.div_norm.
exact: refines_apply.
Qed.

Global Instance refine_ratBigQ_eq :
  refines (r_ratBigQ ==> r_ratBigQ ==> eq) eqtype.eq_op eq_op.
Proof.
rewrite refinesE => _ a <- _ b <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel /=.
rewrite /eq_op /eq_bigQ BigQ.spec_eq_bool.
case: (BigQ.to_Q a) => na da {a}.
case: (BigQ.to_Q b) => nb db {b}.
rewrite /Qeq_bool !Z2int_Qred /= /Zeq_bool -Z.eqb_compare.
rewrite divq_eq ?intq_eq0 ?Posz_nat_of_pos_neq0 //.
rewrite !nat_of_pos_Z_to_pos.
rewrite !gez0_abs; [|by rewrite -[0%R]int2ZK Z2int_le..].
rewrite -!intrM -!Z2int_mul eqr_int.
by case: Z.eqb_spec => [->|eq]; apply/eqP => // eq'; apply/eq/Z2int_inj.
Qed.

Global Instance refine_ratBigQ_eq' :
  refines (r_ratBigQ ==> r_ratBigQ ==> bool_R)%rel eqtype.eq_op eq_op.
Proof.
rewrite refinesE => x1 x2 rx y1 y2 ry.
move: refine_ratBigQ_eq; rewrite refinesE => /(_ _ _ rx _ _ ry) <-.
case: (_ == _); constructor.
Qed.

Global Instance refine_ratBigQ_lt :
  refines (r_ratBigQ ==> r_ratBigQ ==> bool_R) Num.lt lt_op.
Proof.
rewrite refinesE => _ a <- _ b <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel /=.
rewrite /lt_op /lt_bigQ BigQ.spec_compare.
case: (BigQ.to_Q a) => na da {a}.
case: (BigQ.to_Q b) => nb db {b}.
rewrite !Z2int_Qred /= /Qcompare /= -Z.ltb_compare.
rewrite ltr_pdivr_mulr ?ltr0z ?nat_of_pos_gtr0 //.
rewrite mulrAC ltr_pdivl_mulr ?ltr0z ?nat_of_pos_gtr0 //.
rewrite !nat_of_pos_Z_to_pos.
rewrite !gez0_abs; [|by rewrite -[0%R]int2ZK Z2int_le..].
rewrite -!intrM -!Z2int_mul ltr_int.
case: ltP.
{ by move=> /(proj1 (Z2int_lt _ _)) /(proj2 (Z.ltb_lt _ _)) => ->. }
by move=> /(proj1 (Z2int_le _ _)) /(proj2 (Z.ltb_ge _ _)) => ->.
Qed.

Global Instance refine_ratBigQ_le :
  refines (r_ratBigQ ==> r_ratBigQ ==> bool_R) Num.le leq_op.
Proof.
rewrite refinesE => _ a <- _ b <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel /=.
rewrite /leq_op /le_bigQ BigQ.spec_compare.
case: (BigQ.to_Q a) => na da {a}.
case: (BigQ.to_Q b) => nb db {b}.
rewrite !Z2int_Qred /= /Qcompare /=.
rewrite ler_pdivr_mulr ?ltr0z ?nat_of_pos_gtr0 //.
rewrite mulrAC ler_pdivl_mulr ?ltr0z ?nat_of_pos_gtr0 //.
rewrite !nat_of_pos_Z_to_pos.
rewrite !gez0_abs; [|by rewrite -[0%R]int2ZK Z2int_le..].
rewrite -!intrM -!Z2int_mul ler_int.
case: leP.
{ move=> /(proj1 (Z2int_le _ _)) /Zle_compare.
  by rewrite Z.compare_antisym; case: Z.compare. }
by move=> /(proj1 (Z2int_lt _ _)) /Zlt_compare; case: Z.compare.
Qed.

Global Instance refine_ratBigQ_max :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ)%rel Num.max max_op.
Proof.
apply: refines_abstr2 => x1 x2 rx y1 y2 ry.
have H := refines_apply (refines_apply refine_ratBigQ_lt rx) ry.
move: H => /refines_bool_eq; rewrite maxElt refinesE => ->.
rewrite /lt_op /lt_bigQ /max_op /max_bigQ /BigQ.max.
by case: (_ ?= _)%bigQ.
Qed.

Global Instance refine_ratBigQ_min :
  refines (r_ratBigQ ==> r_ratBigQ ==> r_ratBigQ)%rel Num.min min_op.
Proof.
apply: refines_abstr2 => x1 x2 rx y1 y2 ry.
have H := refines_apply (refines_apply refine_ratBigQ_lt ry) rx.
move: H => /refines_bool_eq; rewrite minEle leNgt refinesE => ->.
rewrite /lt_op /lt_bigQ /min_op /min_bigQ /BigQ.min.
rewrite !BigQ.spec_compare -QArith_base.Qcompare_antisym.
by case: QArith_base.Qcompare.
Qed.

Global Instance refine_ratBigQ_of_nat :
  refines (nat_R ==> r_ratBigQ)%rel (fun n => n%:~R%R) cast_op.
Proof.
rewrite refinesE => n _ /nat_R_eq <-; rewrite /r_ratBigQ /bigQ2rat /fun_hrel.
rewrite /= Z_ggcd_1_r /= BigZ.spec_of_Z mulr1.
by apply/eqP; rewrite eqr_int Z2int_Z_of_nat.
Qed.

Global Instance refine_ratBigQ_spec :
  refines (eq ==> r_ratBigQ)%rel spec spec_id.
Proof. by rewrite refinesE => x _ <-. Qed.

Global Instance refine_ratBigQ_bigQ2rat a : refines r_ratBigQ (bigQ2rat a) a.
Proof. by rewrite refinesE. Qed.

End binrat_theory.
