Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
(* Require Import zint orderedalg orderedzint. *)
Require Import dvdring.

Import GRing.Theory.
(* Import OrderedRing.Theory. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

Section Zdiv.

Require Import Coq.ZArith.Zdiv Coq.ZArith.Zabs.
Require Import infra.
Import ssrnat ssralg.

Local Open Scope ring_scope.

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
apply: inj_lt; apply: Zabs_nat_lt; omega.
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


Time Eval compute in (3 %| 4)%Z.
Time Eval compute in (2342 %/ 123)%Z.
Time Eval compute in (123123 %/ 1234)%Z.


Time Eval compute in (gcdr 6685 4011)%Z.
Time Eval compute in (GCD 6685 4011)%Z.
Time Eval compute in (gcdr 11466 1428)%Z.
Time Eval compute in (GCD 11466 1428)%Z.
Time Eval compute in (gcdr 114662 14282)%Z.
Time Eval compute in (GCD 114662 14282)%Z.

End Zdiv.