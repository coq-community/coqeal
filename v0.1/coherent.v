Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice matrix bigop zmodp mxalgebra poly.

Require Import ssrcomplements stronglydiscrete dvdring.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** Coherent rings *)
Module CoherentRing.

(* This is done on the opposite side compared to mxalgebra... *)
Record mixin_of (R : ringType) : Type := Mixin {
  size_solve : forall m, 'rV[R]_m -> nat;
  solve_row : forall m (V : 'rV[R]_m), 'M[R]_(m,size_solve V);
  _ : forall m (V : 'rV[R]_m) (X : 'cV[R]_m),
    reflect (exists Y : 'cV[R]_(size_solve V), X = solve_row V *m Y)
            (V *m X == 0)
}.

Section ClassDef.

(** Coherent rings are based on strongly discrete *)
Record class_of (R : Type) : Type := Class {
  base  : StronglyDiscrete.class_of R;
  mixin : mixin_of (StronglyDiscrete.Pack base R)
}.
Local Coercion base : class_of >-> StronglyDiscrete.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@StronglyDiscrete.Pack T b0 T)) :=
  fun bT b & phant_id (StronglyDiscrete.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition stronglyDiscreteType := StronglyDiscrete.Pack class cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> StronglyDiscrete.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion stronglyDiscreteType : type >-> StronglyDiscrete.type.
Canonical Structure stronglyDiscreteType.

Notation coherentRingType := type.
Notation CoherentRingType T m := (@pack T _ m _ _ id _ id).
Notation CoherentRingMixin := Mixin.
Notation "[ 'coherentRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'coherentRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'coherentRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'coherentRingType'  'of'  T ]") : form_scope.
End Exports.

End CoherentRing.
Export CoherentRing.Exports.

Definition size_solve R := CoherentRing.size_solve (CoherentRing.class R).
Definition solve_row R := CoherentRing.solve_row (CoherentRing.class R).

Section CoherentRingTheory.

Variable R : coherentRingType.

Implicit Types a b c : R.

Lemma solveP : forall m (V : 'rV[R]_m) (X: 'cV[R]_m),
    reflect (exists Y: 'cV[R]_(size_solve V), X = solve_row V *m Y)
    (V *m X == 0).
Proof. by case: R => [? [? []]]. Qed.

Lemma solve_rowP0 m (V : 'rV[R]_m) : V *m solve_row V = 0.
Proof.
rewrite -col_matrixP => i.
rewrite col_mul col0.
apply/eqP/solveP.
exists (delta_mx i 0).
by rewrite colE.
Qed.

Fixpoint size_solveMxN m n : 'M[R]_(m,n) -> nat :=
  match m return 'M[R]_(m,n) -> nat with
    | S p => fun (M: 'M[R]_(1 + _,n)) =>
       size_solveMxN (dsubmx M *m solve_row (usubmx M))
    | _ => fun _ => n
end.

Fixpoint solveMxN m n : 
  forall (M : 'M_(m,n)), 'M_(n,size_solveMxN M) :=
  match m with
    | S p => fun (M : 'M_(1+p,n)) =>
      let G1 := solve_row (usubmx M) in 
      G1 *m solveMxN (dsubmx M *m G1)
    | _ => fun _ => 1%:M
  end.

Lemma solveMxNP : forall m n (M:'M[R]_(m,n)) (X:'cV[R]_n),
  reflect (exists Y, X = solveMxN M *m Y)
          (M *m X == 0).
Proof.
elim => [ m n X | m hi n ].
  rewrite flatmx0 /=.
  apply: (iffP idP) => [_|]; last by rewrite mul0mx.
  by exists X; rewrite mul1mx.
rewrite [m.+1]/(1 + m)%nat => M /=.
set p1 := size_solve (usubmx M).
set G1 := solve_row (usubmx M).
move: (hi _ (dsubmx M *m G1))=> {hi} hi X.
apply: (iffP eqP) => [ hM | [Y hY]].
  have : usubmx M *m X == 0.
    move: (hM).
    rewrite -{1}[M]vsubmxK (@mul_col_mx _ 1 m n 1) => /colP /(_ 0).
    rewrite !mxE.
    case: splitP => // j; rewrite [j]ord1 {j} !mxE => _ h.
    apply/eqP/matrixP => i j.
    rewrite !ord1 {i j} !mxE -[X in _ = X]h.
    by apply/eq_bigr => i // _; rewrite !mxE lshift0.
  case/solveP => V hV.
  have : dsubmx M *m G1 *m V == 0.
    move: hM; rewrite hV mulmxA => /colP hcol.
    apply/eqP/colP => i; move: (hcol (lift 0 i)); rewrite !mxE => h.
    rewrite -[X in _ = X]h.
    apply/eq_bigr => j // _.
    congr (_ * _); rewrite !mxE.
    by apply/eq_bigr => k // _; rewrite !mxE rshift1.
  case/hi => W hW.
  by exists W; rewrite hV hW mulmxA.
set Z : 'M[R]_(1 + m,1) := 0.
rewrite -[M]vsubmxK (@mul_col_mx _ 1) -[Z]col_mx0.
f_equal.
  apply/eqP/solveP.
  exists (solveMxN (dsubmx M *m G1) *m Y); by rewrite mulmxA.
rewrite hY -mulmxA [dsubmx M *m _]mulmxA.
apply/eqP/hi.
by exists Y.
Qed.

Lemma solveMxNP0 : forall m n (M : 'M[R]_(m,n)),
  M *m solveMxN M = 0.
Proof.
elim => [ M | m hi] n; first by rewrite flatmx0 mul0mx.
rewrite [m.+1]/(1 + m)%nat => M /=.
set PP := dsubmx M *m _.
rewrite -{3}[M]vsubmxK -[0 : 'M[R]_(1 + _,_)]vsubmxK (@mul_col_mx _ 1) !mulmxA
        solve_rowP0 mul0mx hi.
by f_equal; apply/matrixP => i j; rewrite !mxE.
Qed.

(** As everything is based on strongly discrete rings we can solve general
   systems of the kind MX = A *)
Fixpoint solveGeneral m n : 'M_(m,n) -> 'cV_m -> option 'cV_n :=
  match m return 'M[R]_(m,n) -> 'cV[R]_m -> option 'cV[R]_n with
   | S p => fun (M: 'M[R]_(1 + _,n)) (A : 'cV[R]_(1 + _)) =>
    let G1 := solve_row (usubmx M) in
    let W1 := member (A 0 0) (usubmx M) in
     obind (fun w1 : 'cV_n =>
       obind (fun S => Some (w1 + G1 *m S))
       (solveGeneral (dsubmx M *m G1) (dsubmx A - dsubmx M *m w1))
     ) W1
   | _ => fun _ _ => Some 0
  end.

CoInductive SG_spec m n (M : 'M[R]_(m,n)) (A : 'cV[R]_m)
  : option 'cV[R]_n -> Type :=
| HasSol X0 of
  (forall (X : 'cV[R]_n),
   reflect (exists Y, X = solveMxN M *m Y + X0)
            (M *m X == A)) : SG_spec M A (Some X0)
| NoSol of (forall X, M *m X != A) : SG_spec M A None.

Lemma solveGeneralP: forall m n (M : 'M[R]_(m,n)) (A : 'cV[R]_m),
  SG_spec M A (solveGeneral M A).
Proof.
elim=> [n M A|m hi n] /=.
- rewrite !flatmx0.
  constructor => X; rewrite mul0mx.
  apply: (iffP eqP) => // _.
  have : (0: 'M[R]_(0,n)) *m X == 0 by rewrite mul0mx.
  case/solveMxNP => Y; exists Y.
  by rewrite addr0.
rewrite [m.+1]/(1 + m)%nat => M A.
case: member_specP => [ x1 hx1 | ] /=.
  case: hi => [ xn hxn | hi ] /=; constructor => X.
    apply : (iffP eqP).
      rewrite -{1}[M]vsubmxK -{1}[A]vsubmxK (@mul_col_mx _ 1).
      case/(@eq_col_mx _ 1) => hl0 hlS.
      have : (usubmx M *m (X - x1) == 0).
        rewrite mulmxBr hl0 -hx1.
        by apply/eqP/matrixP => i j; rewrite !mxE !ord1 lshift0 subrr.
      case/solveP => Y1 /eqP; rewrite subr_eq => /eqP hX.
      move/eqP : hlS; rewrite hX mulmxDr eq_sym -subr_eq eq_sym mulmxA.
      case/hxn => Yn hY1 /=.
      by exists Yn; rewrite hY1 -mulmxA mulmxDr addrAC addrA.
    case => Yn ->.
    rewrite mulmxDr mulmxA solveMxNP0 mul0mx add0r -{1}[M]vsubmxK.
    rewrite (@mul_col_mx _ 1) -[A]vsubmxK !mulmxDr -hx1 mulmxA solve_rowP0.
    rewrite mul0mx addr0.
    f_equal; first by apply/matrixP => i j; rewrite !mxE !ord1 lshift0.
    apply/eqP; rewrite eq_sym addrC -subr_eq eq_sym mulmxA.
    apply/hxn.
    by exists 0; rewrite mulmx0 add0r.
  apply/eqP.
  rewrite -[M]vsubmxK -[A]vsubmxK (@mul_col_mx _ 1).
  case/(@eq_col_mx _ 1)=> h1 h2.
  move: hx1 hi h1 h2.
  have <- : usubmx A = (A 0 0)%:M by apply/matrixP => i j;
    rewrite !mxE !ord1 lshift0.
  set uM := usubmx M.
  set dM := dsubmx M.
  set b  := usubmx A.
  set dA := dsubmx A.
  move=> hx1 hi h1 h2.
  have: uM *m (X - x1) == 0 by rewrite mulmxBr h1 -hx1 subrr.
  case/solveP => Y1 hY1.
  move/eqP : (hi Y1); apply.
  by rewrite -mulmxA -hY1 mulmxBr h2.
move=> hl1; constructor => X; apply/eqP.
rewrite -{1}[M]vsubmxK -{1}[A]vsubmxK (@mul_col_mx _ 1).
case/(@eq_col_mx _ 1) => hl0 hlS.
move/eqP : (hl1 X); apply.
have <- : usubmx A = (A 0 0)%:M by apply/matrixP => i j;
    rewrite !mxE !ord1 lshift0.
by rewrite hl0.
Qed.

End CoherentRingTheory.

(** This section proves that a ring is coherent is the intersection of two
   finitely generated ideals is again finitely generated. It requires that
   the underlying ring (in this case a strongly discrete ring) is an
   integral domain *)
Section IntersectionCoherent.

Variable R : stronglyDiscreteType.

(** The size of the intersection - 1, this is done to ensure that
   the intersection is nonempty *)
Variable cap_size : forall n m, 'rV[R]_n -> 'rV[R]_m -> nat.

(** Intersection of two ideals *)
Variable cap :
  forall n m (I : 'rV[R]_n) (J : 'rV[R]_m), 'rV[R]_(cap_size I J).+1.

Hypothesis cap_spec : forall n m (I : 'rV[R]_n) (J : 'rV[R]_m),
  int_spec (cap I J).

Fixpoint size_int n: 'rV[R]_n -> nat := match n with
  | 0   => fun _ => 0%N
  | S p => fun (V : 'rV[R]_(1 + p)) =>
               let v  := lsubmx V in
               let vs := rsubmx V : 'rV[R]_p in
               ((cap_size v (-vs)).+1 + size_int vs)%N
end.

Definition cap_wl n m (I : 'rV_n) (J : 'rV_m) := subidW (cap I J) I.

Lemma wl n m (I : 'rV_n) (J : 'rV_m) : I *m cap_wl I J = cap I J.
Proof. by symmetry; apply/subidWP; case: cap_spec. Qed.

Definition cap_wr n m (I : 'rV_n) (J : 'rV_m) := subidW (cap I J) J.

Lemma wr n m (I : 'rV_n) (J : 'rV_m) : J *m cap_wr I J = cap I J.
Proof. by symmetry; apply/subidWP; case: cap_spec. Qed.

Fixpoint solve_int m : forall (V : 'rV_m),'M_(m,size_int V) :=
  match m return forall V : 'rV_m, 'M_(m,size_int V) with
    | 0 => fun _ => 0
    | S p => fun (V' : 'rV_(1 + p)) =>
             let v   := lsubmx V' in
             let vs  := rsubmx V' in
             let m0  := solve_int vs in
             let wv  := cap_wl v (-vs) in
             let wvs := cap_wr v (-vs) in
             block_mx (if v == 0 then delta_mx 0 0 else wv) 0
                      (if v == 0 then 0 else wvs)           m0
  end.

Lemma solve_intP : forall m (V : 'rV_m) (X : 'cV_m),
  reflect (exists Y : 'cV[R]_(size_int V), X = solve_int V *m Y)
          (V *m X == 0).
Proof.
elim => [V X | n IH] /=.
  rewrite thinmx0 flatmx0 /solve_int mulmx0.
  apply: (iffP idP) => //= _.
  by exists 0; rewrite mulmx0.
rewrite [n.+1]/(1 + n)%nat => V X.
set v  := lsubmx V.
set vs := rsubmx V.
set x  := usubmx X.
set xs := dsubmx X.
set m0 := solve_int vs.
set wv := cap_wl v (-vs).
set wvs := cap_wr v (-vs).
move: (wl v (-vs)); rewrite -/wv => Hwv.
move: (wr v (-vs)); rewrite -/wvs => Hwvs.
rewrite -[V]hsubmxK -[X]vsubmxK.
case v0 : (v == 0).
  apply: (iffP idP) => /= [|[W ->]].
    rewrite (@mul_row_col _ _ 1) -/v (eqP v0) mul0mx add0r => vs0.
    case: (IH vs xs) => [[A HA]|[]]; last by apply/IH.
    exists (col_mx (const_mx (x 0 0)) A).
    rewrite (@mul_block_col _ 1) -/xs !mul0mx add0r addr0 -rowE row_const HA.
    by f_equal; apply/rowP => i; rewrite !mxE /= !ord1.
  rewrite mulmxA (@mul_row_col _ _ 1) -/v mulmxDl {3}(eqP v0) !mul0mx.
  rewrite add0r -[W]vsubmxK -mulmxA mul_row_col mul0mx add0r.
  apply/IH.
  by exists (dsubmx W).
apply: (iffP idP) => /= [|[W ->]].
  rewrite (@mul_row_col _ _ 1) => hwx.
  have vx00 : ((v * x) 0 0)%:M = v * x
    by apply/matrixP=> i j; rewrite !ord1 !mxE eqxx mulr1n.
  have : member ((v * x) 0 0) (cap v (- vs)).
    case: cap_spec => c /= _ _ in_int.
    apply: in_int; first by apply/memberP; exists x; rewrite vx00.
    apply/memberP; exists xs; apply/eqP.
    by rewrite eq_sym -subr_eq0 mulNmx opprK vx00.
  case/memberP=> W hW.
  case: (IH vs (xs - (wvs *m W))) => [[A HA]|[]].
    exists (col_mx W A).
    rewrite (@mul_block_col _ 1) mul0mx addr0 -HA addrCA subrr addr0.
    f_equal; apply/(@scalemx_inj _ _ _ (v 0 0)).
    (* The proof breaks down here if strongly discrete rings are not idomains! *)
      apply/negP => v00; case/negP: v0; apply/eqP.
      by apply/rowP => i; rewrite !ord1 /= (eqP v00) !mxE.
    by rewrite -!mul_scalar_mx -mx11_scalar mulmxA Hwv hW vx00.
  apply/IH.
  by rewrite mulmxDr mulmxN addrC -mulNmx mulmxA Hwvs hW vx00.
rewrite -[W]vsubmxK (@mul_block_col _ 1) mul0mx addr0 (@mul_row_col _ _ 1).
rewrite !mulmxA Hwv addr_eq0 -mulNmx mulmxDr !mulmxA Hwvs addrC -subr_eq.
rewrite addrN -mulmxA mulNmx eq_sym oppr_eq0.
case: (IH vs _)=> // [[]].
by exists (dsubmx W).
Qed.

Definition int_coherentMixin := CoherentRing.Mixin solve_intP.
(* Canonical Structure int_coherentType := *)
(*   Eval hnf in CoherentRingType R int_coherentMixin. *)

End IntersectionCoherent.

Section BezoutCoherent.

Variable R : bezoutRingType.

Definition bcap_size m n (I : 'rV[R]_m) (J : 'rV[R]_n) := 0%N.

Definition bcap m n (I : 'rV_m) (J : 'rV_n) : 'rV[R]_1 :=
  (lcmr (principal_gen I) (principal_gen J))%:M.

Definition bcap_wl m n (I : 'rV_m) (J : 'rV_n) : 'cV[R]_m :=
  let a := principal_gen I in
  let b := principal_gen J in
  principal_w1 I *m (odflt 0 (b %/? gcdr a b))%:M.

Lemma bcap_wlP m n (I : 'rV_m) (J : 'rV_n) : I *m bcap_wl I J = bcap I J.
Proof.
rewrite /bcap_wl /bcap mulmxA principal_w1_correct mul_scalar_mx.
apply/rowP => i; rewrite !mxE !ord1 {i} /= !mulr1n.
set a := principal_gen _; set b := principal_gen _.
case a0 : (a == 0); first by rewrite (eqP a0) lcm0r mul0r.
case b0 : (b == 0).
  by rewrite (eqP b0) lcmr0 odiv0r /= ?mulr0 // gcdr_eq0 a0.
case: odivrP => /= => [x Hx | H].
  apply/(@mulIf _ (gcdr a b)); first by rewrite gcdr_eq0 a0 b0.
  by rewrite -mulrA -Hx mulr_lcm_gcd.
case/dvdrP: (dvdr_gcdr a b) => x /eqP Hx.
move: (H x).
by rewrite Hx.
Qed.

Definition bcap_wr m n (I : 'rV_m) (J : 'rV_n) : 'cV[R]_n :=
  let a := principal_gen I in
  let b := principal_gen J in
  principal_w1 J *m (odflt 0 (a %/? (gcdr a b)))%:M.

Lemma bcap_wrP n m (I : 'rV_n) (J : 'rV_m) : J *m bcap_wr I J = bcap I J.
Proof.
rewrite /bcap_wl /bcap mulmxA principal_w1_correct mul_scalar_mx.
apply/rowP => i; rewrite !mxE !ord1 {i} /= !mulr1n.
set b := principal_gen _; set a := principal_gen _.
case b0 : (b == 0); first by rewrite (eqP b0) lcmr0 mul0r.
case a0 : (a == 0).
  by rewrite (eqP a0) lcm0r odiv0r /= ?mulr0 // gcdr_eq0 b0 eqxx.
case: odivrP => /= => [x Hx | H].
  apply/(@mulIf _ (gcdr a b)); first by rewrite gcdr_eq0 a0 b0.
  by rewrite -mulrA -Hx mulr_lcm_gcd mulrC.
case/dvdrP: (dvdr_gcdl a b) => x /eqP Hx.
move: (H x).
by rewrite Hx.
Qed.

Lemma bcap_int (x : 'M_1) (m n : nat) (I : 'rV_m) (J : 'rV_n) :
  (exists I' : 'cV_m, I *m I' = x) ->
  (exists J' : 'cV_n, J *m J' = x) ->
   exists W : 'cV_1, bcap I J *m W = x.
Proof.
case => I' HI' [J' HJ'].
move: (principal_w2_correct I).
move: (principal_w2_correct J).
rewrite /bcap /principal.
set a := principal_gen I; set b := principal_gen J => Hb Ha.
have div1 : a %| x 0 0.
  apply/dvdrP.
  exists ((principal_w2 I *m I') 0 0).
  move: HI'.
  rewrite -{1}Ha => <-.
  by rewrite mulrC mul_scalar_mx -scalemxAl !mxE.
have div2 : b %| x 0 0.
  apply/dvdrP.
  exists ((principal_w2 J *m J') 0 0).
  move: HJ'.
  rewrite -{1}Hb => <-.
  by rewrite mulrC mul_scalar_mx -scalemxAl !mxE.
move/dvdrP: (dvdr_lcm a b (x 0 0)).
rewrite div1 div2 /= => [[y Hy]].
exists y%:M.
by rewrite -scalar_mxM mulrC -Hy -mx11_scalar.
Qed.

(* This is a bit ugly... *)
Lemma bcap_spec m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  @int_spec _ _ m n I J (bcap I J).
Proof.
split.
- by apply/subidP; exists (bcap_wl I J); rewrite bcap_wlP.
- by apply/subidP; exists (bcap_wr I J); rewrite bcap_wrP.
move=> /= x.
case/member_subidP/subidP => I' hI'.
case/member_subidP/subidP => J' hJ'.
apply/member_subidP/subidP.
have h1 : exists I'0 : 'cV_m, I *m I'0 = x%:M by exists I'.
have h2 : exists J'0 : 'cV_n, J *m J'0 = x%:M by exists J'.
case: (bcap_int h1 h2) => D hD.
by exists D.
Qed.

Definition bezout_coherentMixin := int_coherentMixin bcap_spec.
Canonical Structure bezout_coherentType :=
  Eval hnf in CoherentRingType R bezout_coherentMixin.

End BezoutCoherent.