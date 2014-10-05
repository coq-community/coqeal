(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype matrix mxalgebra bigop zmodp perm choice.

Require Import dvdring mxstructure minor edr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section Smith2x2.

Variable R : dvdRingType.

Variable smith2x2 : 'M[R]_2 -> 'M[R]_2 * seq R * 'M[R]_2.

Definition smith1xn n (smith2xn : 'M[R]_(2,n.+2) -> 'M[R]_2 * seq R * 'M[R]_n.+2)
  (M : 'M[R]_(1,n.+2)) : 'M[R]_1 * seq R * 'M[R]_n.+2 :=
  let: (L,d,R) := smith2xn (col_mx M 0) in
  if d`_0 == 0 then (1%:M,[::],1%:M) else ((L 0 0)%:M, [:: d`_0], R).

Fixpoint smith2xn n : 'M[R]_(2,1 + (1 + n)) -> 'M[R]_2 * seq R * 'M[R]_n.+2 :=
  match n with
  | 0 => fun A => smith2x2 A
  | n.+1 => fun A : 'M[R]_(2,1 + _) =>
    let: A1 := lsubmx A in let: A2 := rsubmx A in
    let: (P1,d1,Q1) := smith2xn A2 in
    let: C := row_mx (P1 *m A1) (P1 *m A2 *m Q1) : 'M[R]_(2,1 + (1 + _)) in
    let: D := row_mx (col 0 C) (col 1 C) in
    let: E := rsubmx (rsubmx C) in
    let: (P2,d2,Q2) := smith2x2 D in
    let: H := row_mx (P2 *m D *m Q2) (P2 *m E) : 'M[R]_(1 + 1, 1 + _) in
    let: y := d2`_0 in
    let: r' := map_mx (fun x => odflt 0 (x %/? y)) (ursubmx H) in
    let: H' := drsubmx H : 'rV_(2 + _) in
    let: (L1,d,R1) := smith1xn smith2x2 (lsubmx H') in
    let: R1' :=  (block_mx R1 0 0 1%:M) in
    (lift0_mx L1 *m P2 *m P1,
     y :: d,
     lift0_mx Q1 *m block_mx Q2 0 0 1%:M *m block_mx 1%:M (- r' *m R1') 0 R1')
  end.

Fixpoint smithmxn_rec m n : 'M[R]_(1 + (1 + m),1 + (1 + n)) ->
 'M[R]_(1 + (1 + m)) * seq R * 'M[R]_(1 + (1 + n)) := match m,n with
  | 0,_ => fun A => smith2xn A
  | _,0 => fun A => let: (L,d,R) := smith2xn A^T in (R^T,d,L^T)
  | m'.+1,n'.+1 => fun A =>
     let: A1 := usubmx A in let: A2 := dsubmx A in
     let: (P1,x,Q1) := smithmxn_rec A2 in
     let: C := col_mx (A1 *m Q1) (P1 *m A2 *m Q1) in
     let: D := col_mx (row 0 C) (row 1 C) in
     let: E := dsubmx (dsubmx C) in
     let: (P2,y,Q2) := smith2xn D in
     let: H := col_mx (P2 *m D *m Q2) (E *m Q2) : 'M[R]_(1 + _, 1 + _) in
     let: y := y`_0 in
     let: c' := map_mx (fun x => odflt 0 (x %/? y)) (dlsubmx H) in
     let: (L1,d,R1) := smithmxn_rec (drsubmx H) in
     let: P := block_mx P2 0 0 1%:M : 'M[R]_(1 + _) in
    (block_mx 1%:M 0 (- L1 *m c') L1 *m P *m lift0_mx P1,
     y :: d,
     Q1 *m Q2 *m lift0_mx R1)
  end.

Definition smithmxn m n : 'M[R]_(m,n) -> 'M[R]_m * seq R * 'M[R]_n :=
  match m,n with
    | 0,_ => fun _ => (1%:M,[::],1%:M)
    | _,0 => fun _ => (1%:M,[::],1%:M)
    | 1,1 => fun A => (1%:M,[:: A 0 0],1%:M)
    | 1,_.+2 => smith1xn (@smith2xn _)
    | _.+2,1 => fun A => let: (L,d,R) := smith1xn (@smith2xn _) A^T
                         in (R^T,d,L^T)
    | _.+2,_.+2 => fun A => smithmxn_rec A
  end.

End Smith2x2.

Let simplmx := (mulmx1,mul1mx,mul0mx,mulmx0,addr0,add0r).

Section Smith2x2_correctness.

Variable R : dvdRingType.

Variable smith2x2 : 'M[R]_2 -> 'M[R]_2 * seq R * 'M[R]_2.

Hypothesis smith2x2P : forall M, smith_spec M (smith2x2 M).

Lemma surgery m n (M : 'M[R]_(1 + (1 + m),n)) :
  M = col_mx (col_mx (row 0 M) (row 1 M)) (dsubmx (dsubmx M)).
Proof.
apply/matrixP=> i j; rewrite !mxE; case: splitP=> k hk; rewrite !mxE.
  by case: splitP=> l hl; rewrite !mxE; congr fun_of_matrix;
     apply/ord_inj; rewrite hk hl ord1.
by congr fun_of_matrix; apply/ord_inj.
Qed.

Lemma surgery2 m n (M : 'M[R]_(m,1 + (1 + n))) :
  M = row_mx (row_mx (col 0 M) (col 1 M)) (rsubmx (rsubmx M)).
Proof.
apply: trmx_inj; rewrite (tr_row_mx (row_mx (col 0 M) (col 1 M))).
by rewrite tr_row_mx !tr_col !trmx_rsub {1}[M^T]surgery.
Qed.

Hint Resolve dvdr0.

Lemma smith1xnP n (M : 'M[R]_(1,1 + (1 + n)))
  (smith2xn : 'M[R]_(2,n.+2) -> 'M[R]_2 * seq R * 'M[R]_n.+2)
  (smith2xnP : forall M, smith_spec M (smith2xn M))  :
  smith_spec M (smith1xn smith2xn M).
Proof.
rewrite /smith1xn; case: smith2xnP; rewrite [2]/(1+1)%N=> P d Q h_eq hs hP hQ.
have [d0|d_neq0] := (boolP (d`_0 == 0)).
  constructor; rewrite ?unitmx1 // ?simplmx; apply/matrixP=> i j.
  move/(canRL (mulmxK hQ))/(canRL (mulKmx hP))/matrixP: h_eq.
  rewrite diag_mx_seq0; last by rewrite sorted_dvd0r // sorted_cons // dvd0r.
  rewrite mul0mx mulmx0 ord1 {i} diag_mx_seq_nil.
  by move=> /(_ (widen_ord (lt0n 2) 0) j); rewrite !mxE split1; case: unliftP.
move/matrixP: h_eq; rewrite -mulmxA [col_mx M 0 *m _]mul_col_mx mul0mx=> h_eq.
have hP00 : ((P 0 0)%:M : 'M_1) \in unitmx.
  rewrite unitmxE det_scalar expr1; apply/unitrPr; exists ((invmx P) 0 0).
  move/matrixP: (mulVmx hP) => /(_ 0 0); rewrite !mxE !big_ord_recl big_ord0.
  suff -> : P (lift 0 0) 0 = 0 by rewrite mulr0 !addr0 mulrC.
  rewrite -{1}[P]submxK (mul_block_col (ulsubmx P)) ?(mulmx0,addr0) in h_eq.
  move/eqP: (h_eq 1 0) (h_eq 0 0) d_neq0.
  rewrite ?(mxE,mulr0n,split1); case: unliftP unliftP=> // i _ [] //= _.
  rewrite ord1 ?(mxE,big_ord_recl,big_ord0) addr0 lshift0 rshift1 mulr1n.
  by rewrite mulf_eq0; case/orP=> /eqP -> // <-; rewrite mulr0 addr0 eqxx.
constructor=> //; apply/matrixP=> i j; rewrite ord1 {i}.
move: (h_eq 0 j); rewrite ?(big_ord_recl,big_ord0,addr0,mxE,split1,mulr1n).
case: unliftP unliftP => // _ [] //= k _ <-.
rewrite ?(ord1,mxE,big_ord_recl,mulr0,addr0,mulrDr,mulrA) {k} big_distrr /=.
by do ?congr (_ + _); apply: eq_bigr=> i _; rewrite ?(mxE,big_ord1) mulrA.
Qed.

Arguments nth : simpl never.

Lemma smith2xnP : forall n (M : 'M[R]_(2,1 + (1 + n))),
  smith_spec M (smith2xn smith2x2 M).
Proof.
elim=> [|n ih]; first exact: smith2x2P.
rewrite [n.+1]/(1 + n)%N => M /=; set A1 := lsubmx M; set A2 := rsubmx M.
case: ih=> /= P1 d1 Q1 h1 h2 hP1 hQ1; set E := rsubmx _.
set C := row_mx (P1 *m A1) _ : 'M[R]_(2,1 + (1 + _)); set D := row_mx _ _.
case: smith2x2P=> /= P2 d2 Q2 H1 H2 hP2 hQ2.
set H := row_mx (P2 *m D *m Q2) _ : 'M[R]_(1 + _, 1 + (1 + _)).
case: (smith1xnP _ smith2x2P)=> L1 d R1; rewrite -mulmxA=> hLdR dsorted hL1 hR1.
set r := ursubmx H; set r' := map_mx _ _; set H' := drsubmx H : 'rV[R]_(2 + n).
have dvd_d20_d0 : d2`_0 %| d1`_0.
  have -> : d1`_0 = D 0 (rshift 1 0).
    rewrite row_mxEr !mxE split1 h1; case: unliftP => //= j hj.
    by rewrite !mxE; case: j hj=> [[]].
  move/(canRL (mulmxK hQ2))/(canRL (mulKmx hP2)): H1 => ->.
  apply: dvdr_mulmxl=> i j; apply: dvdr_mulmxr=> {i j} i j.
  by rewrite !mxE; case: (i == j :> nat); rewrite ?sorted_nth0 ?mulr0n.
have hx0 i j : d1`_0 %| d1`_i *+ (i == j).
  by case: (i == j :> nat); rewrite ?sorted_nth0 // mulr0n dvdr0.
have Hdvd i j : d2`_0 %| H i j.
  rewrite -[(1 + (1 + _))%N]/(2 + _)%N /H H1 dvdr_row_mx //; split=> {i j} i j.
    by rewrite !mxE; case: (i == j :> nat); rewrite ?sorted_nth0 ?mulr0n.
  apply: dvdr_mulmxl=> {i j} i j; rewrite /E row_mxKr h1 !mxE.
  move: (dvdr_trans dvd_d20_d0 (hx0 i (rshift 1 j))).
  by case: (i == _ :> nat); rewrite ?(mulr0n,dvdr0,mulr1n).
constructor; rewrite ?unitmx_mul; last first.
- rewrite !unitmxE ?(det_lblock,det_ublock,det_lblock Q2,det1,mulr1,mul1r).
  by rewrite-!unitmxE hQ1 hQ2 hR1.
- by rewrite hP2 hP1 unitmxE (@det_ublock _ 1) det1 mul1r -unitmxE hL1.
- apply: sorted_cons=> //; move/matrixP: hLdR => /(_ 0 0).
  rewrite [RHS]mxE mulr1n => <-.
  exact: (dvdr_mulmxl _ (dvdr_mulmxr _ (dvdr_lsubmx (n0:=2) (dvdr_drsubmx _)))).
rewrite -[M]hsubmxK -/A1 -/A2 -[_ *m P1 *m _]mulmxA (mul_mx_row _ A1) -!mulmxA.
rewrite [row_mx (P1 *m A1) _ *m (_ *m _)]mulmxA mul_row_block ?simplmx !mulmxA.
have -> : lift0_mx L1 *m P2 *m C *m block_mx Q2 0 0 1%:M =
          lift0_mx L1 *m block_mx d2`_0%:M r 0 H'.
  rewrite -!mulmxA; congr (_ *m _); rewrite mulmxA [C]surgery2 -mulmxA.
  rewrite (mul_row_block D) ?simplmx mul_mx_row mulmxA -/H -[H]submxK.
  f_equal; apply/rowP=> i; rewrite !mxE H1 ?ord1 ?lshift0;
  by case: splitP=> // j hj; rewrite !mxE -hj.
rewrite -[lift0_mx L1 *m _ *m _]mulmxA (mulmx_block d2`_0%:M r) ?simplmx.
rewrite mulmx_block ?simplmx mulmxA -mulmxDl mulmxN mul_scalar_mx.
have -> : - (d2`_0 *: r') + r = 0.
  apply/rowP=> i; rewrite 4!mxE.
  case: odivrP=> /= [w ->|]; first by rewrite mulrC addrC subrr mxE.
  move: (Hdvd (lshift _ 0) (rshift 1 i)); rewrite -[H]submxK block_mxEur.
  by case/dvdrP=> w hw /(_ w); rewrite hw eqxx.
rewrite mul0mx diag_mx_seq_cons; f_equal; rewrite -[H']hsubmxK mulmxA.
rewrite (mul_mx_row _ (lsubmx H')) (mul_row_block (L1 *m lsubmx H')) ?simplmx.
rewrite -mulmxA hLdR; apply/rowP=> i; rewrite !mxE.
case: splitP=> j ->; rewrite !mxE //= mulr0n big_ord1 !mxE /H' /E row_mxKr h1.
case: splitP=> [[[] // []]|] //= [[]] //= m hm hh.
by rewrite !mxE big_ord_recl big_ord1 ?(mxE,mulr0n,mulr0,addr0).
Qed.

Arguments smith2xn : simpl never.

Lemma smithmxn_recP : forall m n (M : 'M[R]_(1 + (1 + m),1 + (1 + n))),
  smith_spec M (smithmxn_rec smith2x2 M).
Proof.
elim=> [|m ih [|n] A] /=; first exact: smith2xnP.
  case: smith2xnP=> L0 d R0 h1 h2 h3 h4.
  constructor; rewrite ?unitmx_tr //; apply/trmx_inj.
  by rewrite !trmx_mul !trmxK tr_diag_mx_seq mulmxA.
set A1 := usubmx A; set A2 := dsubmx A.
case: (ih) => P1 x Q1 hP1xQ1 x_sorted hP1 hQ1; rewrite hP1xQ1.
set C := col_mx (A1 *m Q1) _; set D := col_mx (row 0 C) (row 1 C).
set E := dsubmx (dsubmx C).
case: smith2xnP=> P2 y Q2 hP2yQ2 y_sorted hP2 hQ2.
set H := col_mx (P2 *m D *m Q2) (E *m Q2) : 'M[R]_(1 + (1 + _),1 + (1 + _)).
set y0 := y`_0; set c := dlsubmx H; set c' := map_mx _ _; set H' := drsubmx H.
case: ih=> L1 d R1; rewrite -mulmxA=> hLdR d_sorted hL1 hR1.
have dvd_y0_x0 : y0 %| x`_0.
  have -> : x`_0 = D (rshift 1 0) 0.
    rewrite col_mxEd !mxE split1.
    by case: unliftP=> // [[[]]] //= i _; rewrite !mxE.
  move/(canRL (mulmxK hQ2))/(canRL (mulKmx hP2)): hP2yQ2=> ->.
  apply: dvdr_mulmxl=> i j; apply: dvdr_mulmxr=> {i j} i j.
  by rewrite !mxE; case: (i == j :> nat); rewrite ?sorted_nth0 ?mulr0n.
have hx0 i j : x`_0 %| x`_i *+ (i == j).
  by case: (i == j :> nat); rewrite ?sorted_nth0 // mulr0n dvdr0.
have Hdvd i j : y0 %| H i j.
  rewrite -[(1 + (1 + _))%N]/(2 + _)%N; apply: dvdr_col_mx; split=> {i j} i j.
    rewrite hP2yQ2 !mxE.
    by case: (i == j :> nat); rewrite ?sorted_nth0 // mulr0n dvdr0.
  apply: dvdr_mulmxr=> {i j} i j; rewrite /E col_mxKd.
  apply: dvdr_dsubmx=> {i j} i j; rewrite !mxE.
  move: (dvdr_trans dvd_y0_x0 (hx0 i j)).
  by case: (i == j :> nat); rewrite ?(mulr0n,dvdr0,mulr1n).
constructor; last first.
- by rewrite !unitmx_mul hQ1 hQ2 unitmxE det_lblock det1 mul1r -unitmxE.
- rewrite !unitmx_mul /lift0_mx ?(unitmxE,det_lblock,@det_lblock _ 2,det1,mul1r).
  by rewrite mulr1 -!unitmxE hL1 hP1 hP2.
- apply: sorted_cons=> //.
  move/matrixP: hLdR => /(_ 0 0); rewrite [RHS]mxE mulr1n => <-.
  exact: (dvdr_mulmxl L1 (dvdr_mulmxr R1 (dvdr_drsubmx Hdvd))).
rewrite -[A]vsubmxK -!mulmxA [_ *m (col_mx A1 _ *m _)]mulmxA mul_block_col.
rewrite !mul0mx addr0 add0r mul1mx [_ *m (Q1 *m _)]mulmxA [_ *m Q1]mul_col_mx.
rewrite hP1xQ1 [_ *m (C *m _)]mulmxA [_ *m (Q2 *m _)]mulmxA diag_mx_seq_cons.
have -> : block_mx P2 0 0 1%:M *m C *m Q2 = block_mx y0%:M 0 c H'.
  rewrite [C]surgery mul_block_col ?simplmx mul_col_mx -/H -[H]submxK.
  f_equal; apply/rowP=> i; rewrite !mxE hP2yQ2;
  by case: splitP=> // j hj; rewrite !mxE -hj.
rewrite !mulmx_block ?simplmx -hLdR; congr block_mx.
rewrite -mulmxA mulNmx -mulmxN -mulmxDr mul_mx_scalar.
suff -> : - (y0 *: c') + c = 0 by rewrite mulmx0.
apply/colP=> i; rewrite 4!mxE.
case: odivrP=> /= [w ->|]; first by rewrite mulrC addrC subrr mxE.
move: (Hdvd (rshift 1 i) (lshift _ 0)); rewrite -[H]submxK block_mxEdl.
by case/dvdrP=> w hw /(_ w); rewrite hw eqxx.
Qed.

Lemma smithmxnP : forall m n (M : 'M[R]_(m,n)),
  smith_spec M (smithmxn smith2x2 M).
Proof.
case=> [|[[|[|n M]]|m [|[M|n M]]]] /=;
  do ?by constructor; rewrite ?unitmx1 ?flatmx0 ?thinmx0 ?diag_mx_seq_nil.
- constructor; rewrite ?unitmx1 // mul1mx mulmx1.
  by apply/rowP=> i; rewrite ord1 !mxE.
- exact: (smith1xnP _ (@smith2xnP _)).
- case: (smith1xnP _ (@smith2xnP _))=> L1 d R1 h1 h2 h3 h4.
  constructor; rewrite ?unitmx_tr //.
  by apply/trmx_inj; rewrite !trmx_mul !trmxK tr_diag_mx_seq mulmxA.
exact: smithmxn_recP.
Qed.

End Smith2x2_correctness.

(* Bézout domains are Hermite rings *)
Section Bezout_hermite.

Variable R : bezoutDomainType.

Definition hermite (M : 'M[R]_2) := Bezout_step (M 0 0) (M 1 0) M 0.

Lemma hermite10 M : (hermite M) 1 0 = 0.
Proof.
rewrite /hermite Bezout_stepE /Bezout_mx /combine_mx.
rewrite !mxE !big_ord_recl big_ord0 addr0 /=.
case: egcdrP=> g u v a1 b1 heq hg ha1 hb1.
rewrite ?(mxE,mulr0n,mulr1n,mulr0,mulr1,addr0,add0r) /=.
have -> : lift 0 0 = 1 by move=> n; apply/ord_inj.
by rewrite ha1 hb1 !mulrA -mulrDl [a1 * b1]mulrC -mulrDl addrC subrr !mul0r.
Qed.

End Bezout_hermite.

Section Mx2.

Variable R : comRingType.

Definition mx2 a b c d := block_mx (a%:M : 'M[R]_1) b%:M c%:M d%:M.

Lemma mx2_E00 a b c d : (mx2 a b c d) 0 0 = a.
Proof.
by do ?(rewrite mxE split1; case: unliftP=> //=); rewrite mxE mulr1n.
Qed.

Lemma mx2_E01 a b c d : (mx2 a b c d) 0 1 = b.
Proof.
by do ?(rewrite mxE split1; case: unliftP=> //= * ); rewrite ord1 mxE mulr1n.
Qed.

Lemma mx2_E10 a b c d : (mx2 a b c d) 1 0 = c.
Proof.
by do ?(rewrite mxE split1; case: unliftP=> //= * ); rewrite ord1 mxE mulr1n.
Qed.

Lemma mx2_E11 a b c d : (mx2 a b c d) 1 1 = d.
Proof.
have -> : 1 = rshift 1 0 :> 'I_2 by apply/ord_inj.
by rewrite block_mxEdr mxE mulr1n.
Qed.

Lemma detmx2 a b c d : \det (mx2 a b c d) = a * d - c * b.
Proof. by rewrite det2 mx2_E00 mx2_E01 mx2_E10 mx2_E11. Qed.

End Mx2.

(* The necessary and sufficient first order condition in Kaplanskys paper *)
Section Kaplansky_suff.

Variable R : bezoutDomainType.

Variable kap : R -> R -> R -> R * R.

Hypothesis kapP : forall (a b c : R),
  gcdr a (gcdr b c) %= 1 ->
  let: (p,q) := kap a b c in coprimer (p * a) (p * b + q * c).

Lemma coprimerP (a b : R) :
  reflect (exists xy, xy.1 * a + xy.2 * b = 1) (coprimer a b).
Proof.
case: (egcdrP a b) => g u v a1 b1 h1 h2 h3 h4.
apply: (iffP idP)=> [/(eqd_trans h2) | [[x y]]] /=.
  rewrite -unitd1; case/unitrP=> x [hx1 hx2]; exists (x*u,x*v).
  by rewrite -!mulrA -mulrDr h3 h4 !mulrA -mulrDl h1 mul1r.
rewrite {1}h3 {1}h4 !mulrA -mulrDl=> H; move: (@unitr1 R).
rewrite -H unitrM !unitd1=> /andP [_ H'].
by rewrite /coprimer eqd_sym (eqd_trans _ h2) // eqd_sym.
Qed.

Definition kapW a b c : R * R :=
  let: (p,q) := kap a b c in
  if coprimerP (p * a) (p * b + q * c) is ReflectT P
     then projT1 (sig_eqW P) else (0,0).

Lemma kapWP a b c :
  let: (p,q) := kap a b c  in coprimer (p * a) (p * b + q * c) ->
  let: (x,y) := kapW a b c in x * (p * a) + y * (p * b + q * c) = 1.
Proof.
rewrite /kapW; case: kap => p q.
case: coprimerP=> // [[[x y]]] /= Hxy _.
by case: sig_eqW=> /= [[]].
Qed.

Definition egcdr3 (a b c : R) :=
  let: (g',u1,v1,b1,c1) := egcdr b c in
  let: (g,u,v,a1,g1)    := egcdr a g' in
  (g, u, v * u1, v * v1, a1,b1 * g1,c1 * g1).

CoInductive egcdr3_spec a b c : R * R * R * R * R * R * R-> Type :=
  EgcdrSpec g x y z a1 b1 c1 of x * a1 + y * b1 + z * c1 = 1
  & g %= gcdr a (gcdr b c)
  & a = a1 * g & b = b1 * g & c = c1 * g : egcdr3_spec a b c (g,x,y,z,a1,b1,c1).

Lemma egcdr3P a b c : egcdr3_spec a b c (egcdr3 a b c).
Proof.
rewrite /egcdr3; case: egcdrP=> /= g' u1 v1 b1 c1 heq hg' hb1 hc1.
case: egcdrP=> /= g u v a1 g1 heq' hg ha1 hg1.
constructor; rewrite -?mulrA -?hg1 ?(eqd_trans hg) ?eqd_gcd //.
by rewrite -addrA -mulrDr !mulrA -mulrDl heq mul1r.
Qed.

Definition kap_smith (M : 'M[R]_2) : 'M[R]_2 * seq R * 'M[R]_2 :=
  let: A := hermite M in
  let: a00 := A 0 0 in let: a01 := A 0 1 in let: a11 := A 1 1 in
  let: (d,_,_,_,a,b,c) := egcdr3 a00 a01 a11 in
  if d == 0 then (Bezout_mx (M 0 0) (M 1 0) 0,[::],1%:M) else
    let: (p,q) := kap a b c in
    let: (x1,y1) := kapW a b c in
    let: (x,y) := (a * x1 + y1 * b, c * y1) in
     (mx2 p q (- y) x *m Bezout_mx (M 0 0) (M 1 0) 0,
      map (fun x => d * x) [:: 1; - a * c],
      mx2 x1 (p * b + q * c) y1 (- p * a)).

Arguments map : simpl never.

Lemma kap_smithP (M : 'M[R]_2) : smith_spec M (kap_smith M).
Proof.
rewrite /kap_smith; set A := hermite _ : 'M_(1+1).
set a00 := (_ 0 0); set a01 := (_ 0 1); set a11 := (_ 1 1).
case: egcdr3P=> /= d xd yd zd a b c heq; rewrite eqd_sym=> hgcd ha hb hc.
have [d0|dn0] := boolP (d == 0).
  constructor; rewrite ?unitmx1 ?unit_Bezout_mx // mulmx1 -Bezout_stepE.
  have -> : Bezout_step (M 0 0) (M 1 0) M 0 = A by [].
  rewrite diag_mx_seq_nil -(@block_mx0 _ 1 _ 1).
  have -> : A = mx2 a00 a01 0 a11.
    rewrite -[A]submxK.
    congr block_mx; apply/rowP=> i; rewrite !mxE ord1 ?lshift0 ?mulr1n ?rshift1 //;
    have -> // : lift 0 0 = 1 by move=> n; apply/ord_inj.
    by rewrite hermite10.
  by rewrite /mx2; f_equal; rewrite ?ha ?hb ?hc ?(eqP d0) ?mulr0 -scalemx1 scale0r.
have /kapP : gcdr a (gcdr b c) %= 1.
  rewrite -(eqd_mul2r _ _ dn0) mul1r (eqd_trans _ hgcd) //.
  rewrite (eqd_trans (mulr_gcdl _ _ _)) //.
  by rewrite -ha eqd_gcd ?(eqd_trans (mulr_gcdl _ _ _)) // -hb -hc.
move: (kapWP a b c); case: kap => p q H1 H3; move: (H1 H3).
case: kapW=> x1 y1 => {H1 H3} H; move: (H).
rewrite mulrCA [x1 * a]mulrC mulrDr [y1 * _]mulrCA addrA -mulrDr.
set x := a * x1 + y1 * b; rewrite mulrCA [y1 * c]mulrC; set y := c * y1=> Hxy.
constructor.
* set M1 := mx2 _ _ _ _; set M2 := mx2 _ _ _ _.
  rewrite -!mulmxA [_ *m (_ *m M2)]mulmxA -Bezout_stepE.
  have -> : Bezout_step (M 0 0) (M 1 0) M 0 = d *: mx2 a b 0 c.
    rewrite scale_block_mx -!mul_scalar_mx -!scalar_mxM mulr0 mulrC -ha mulrC.
    rewrite -hb -mulrC -hc -[Bezout_step _ _ _ _](@submxK _ 1).
    have h1 : lift 0 0 = 1 by move=> n; apply/ord_inj.
    f_equal; apply/rowP=> i; rewrite !mxE ord1 ?(lshift0,rshift1,h1) mulr1n //.
    by rewrite hermite10.
  rewrite -scalemxAl -!scalemxAr -diag_mx_seq_scale; congr (_ *: _).
  rewrite /M1 /M2 /mx2 !(@mulmx_block _ 1) -[0%:M]scalemx1 scale0r !mul0mx.
  rewrite  !add0r -?(scalar_mxM,raddfD) /= mulrC [_ * y1]mulrC.
  rewrite !diag_mx_seq_cons diag_mx_seq_nil.
  f_equal.
  - by rewrite mulrC Hxy.
  - rewrite [a * _ + _]addrC [a * _]mulrDr addrA mulrCA [a * _]mulrCA.
    rewrite [b * a]mulrC mulNr addNr add0r ![_ * (- p * _)]mulrCA mulNr.
    by rewrite [c * _]mulrC [q * (_ * _)]mulrCA addrN -[0%:M]scalemx1 scale0r.
  - by rewrite -/x -/y mulNr mulrC addNr -[0%:M]scalemx1 scale0r.
  - apply/matrixP=> i j; rewrite !ord1 {i j} [RHS]mxE split1.
    case: unliftP=> //= _; rewrite [RHS]mxE split1; case: unliftP => //= _.
    rewrite !mxE !mulr1n !mulrDr !mulNr !mulrN opprK [_ + y * _]addrC addrA.
    rewrite [p * b]mulrC [a * (b * p)]mulrCA [p * a]mulrC addrN sub0r.
    rewrite ![_ * (a * _)]mulrCA -!mulNr -mulrDr mulrCA mulrAC -mulrA -mulrDr.
    by rewrite [x * p]mulrC addrC -mulrA Hxy mulr1.
* by apply: sorted_cons => //=; rewrite mulr1 dvdr_mulr.
* rewrite !unitmx_mul unit_Bezout_mx !unitmxE detmx2 /x /y mulNr opprK.
  by rewrite [_ * q]mulrC Hxy unitr1.
by rewrite unitmxE detmx2 mulNr mulrN -opprD -mulN1r unitrMl ?unitrN1 // H unitr1.
Qed.

End Kaplansky_suff.

Section Kaplansky_necc.

Variable R : edrType.

Variables a b c : R.

Lemma kapP : gcdr a (gcdr b c) %= 1 ->
             exists p q, coprimer (p * a) (p * b + q * c).
Proof.
case: (smithP (mx2 a b 0 c))=> /= P d Q; rewrite -dvdr1.
set D := diag_mx_seq _ _ _ => heq hsorted P_unitmx Q_unitmx Hgcd.
exists (P 0 0); exists (P 0 1).
suff [[x y /=]] : exists xy, xy.1 * (P 0 0 * a) +
                             xy.2 * (P 0 0 * b + P 0 1 * c) %= 1.
  rewrite -unitd1; case/unitrP=> z [hz1 _].
  by apply/coprimerP; exists (z*x,z*y); rewrite -!mulrA -mulrDr.
exists (Q 0 0,Q 1 0)=> /=.
suff : (D 0 0) \is a GRing.unit.
  rewrite -unitd1 -heq; do 2!(rewrite !mxE big_ord_recl big_ord1).
  rewrite big_ord_recl big_ord1 mx2_E00.
  have -> : lift 0 0 = 1 :> 'I_2 by apply/ord_inj.
  by rewrite mx2_E10 mx2_E11 mx2_E01 mulr0 addr0 mulrC [_ * Q 1 0]mulrC.
rewrite unitd1 -dvdr1; apply/(dvdr_trans _ Hgcd).
have Hij : forall i j, D 0 0 %| (mx2 a b 0 c) i j.
  rewrite (canRL (mulKmx P_unitmx) (canRL (mulmxK Q_unitmx) heq)).
  apply: dvdr_mulmxl; apply: dvdr_mulmxr=> i j; rewrite !mxE.
  case: (i == j :> nat); last by rewrite mulr0n dvdr0.
  rewrite !mulr1n; exact: sorted_nth0.
rewrite !dvdr_gcd; move: (Hij 0 0) (Hij 0 1) (Hij 1 1).
by rewrite mx2_E00 mx2_E01 mx2_E11=> -> -> ->.
Qed.

End Kaplansky_necc.

Section AdequacyGdco.

Variable R : gcdDomainType.

CoInductive adequate_spec (a b : R) : R -> Type :=
  | AdequateSpec0 of b = 0 : adequate_spec a b 0
  | AdequateSpec r of b != 0
                      & r %| b
                      & coprimer r a
                      & (forall d, d * r %| b -> d \isn't a GRing.unit ->
                          ~~ coprimer d a)
                      : adequate_spec a b r.

CoInductive gdco_spec (a b : R) : R -> Type :=
  | GdcoSpec0 of b = 0 : gdco_spec a b 0
  | GdcoSpec r of b != 0
                  & r %| b
                  & coprimer r a
                  & (forall d, d %| b -> coprimer d a -> d %| r)
                  : gdco_spec a b r.

Lemma adequate_gdco a b r : adequate_spec a b r -> gdco_spec a b r.
Proof.
move=> [->|]; first by constructor => //; rewrite eqxx.
move=> {r} r b_neq0 dvd_rb cra /= Hs; constructor=> //=.
move=> /= d dvd_db cda; have [du|dnu] := boolP (d \is a GRing.unit).
  by rewrite dvdUr ?eqd1.
case: dvdrP dvd_rb => // [[s ->]] _ in Hs dvd_db *.
rewrite -(@euclid _ s) // /coprimer 1?mulrC // -unitd1.
apply: (contraLR (Hs _ _)); first by rewrite dvdr_mul // dvdr_gcdr.
rewrite /coprimer -(eqd_ltrans (gcdrA _ _ _)).
exact: coprimer_dvdr (dvdr_gcdr _ _) _.
Qed.

Lemma gdco_adequate a b r : gdco_spec a b r -> adequate_spec a b r.
Proof.
move=> [|/= {r} r b_neq0 rb cra Hd]; first by constructor.
constructor => //= d dr_dvd_b; apply: contra => cda.
case: dvdrP rb => [[s ->]|//] {b} _ in Hd dr_dvd_b b_neq0 *.
have r_neq0 : r != 0 by move: b_neq0; rewrite mulf_eq0 negb_or => /andP [].
have := Hd _ dr_dvd_b.
rewrite -[r as X in _ %| X]mul1r dvdr_mul2r // dvdr1 unitd1; apply.
by rewrite coprimer_mull cra cda.
Qed.

End AdequacyGdco.

Section AdequacyEDR.

Variable R : bezoutDomainType.

Variable gdco : R -> R -> R.
Hypothesis gdcoP : forall p q, gdco_spec p q (gdco p q).

Lemma coprimer_gdco q p : p != 0 -> coprimer (gdco q p) q.
Proof. by case: gdcoP => [->|//]; rewrite eqxx. Qed.

Definition gdco_kap (a b c : R) : R * R :=
  let: (_, x, y, z, _, _, _) := egcdr3 a b c in
  if a == 0 then (y, z)
  else let: r := gdco c a in
       let: (g, _, v, _, _) := egcdr r c in
       if (1 - b) %/? g is Some k' then (1, k' * v) else (1, 0).

Lemma gdco_kapP (a b c : R) : gcdr a (gcdr b c) %= 1 ->
  let: (p, q) := gdco_kap a b c in coprimer (p * a) (p * b + q * c).
Proof.
rewrite /gdco_kap /=.
have [g /= x y z a1 b1 c1] := egcdr3P a b c.
move=> Habc1 /eqd_ltrans <- Ha Hb Hc g_eq1.
move: Habc1 g_eq1 => /(congr1 ( *%R^~ g)); rewrite !mulrDl mul1r.
rewrite -!mulrA -Ha -Hb -Hc {Ha Hb Hc} => <- Habc {g a1 b1 c1}.
move: Habc; have [->|an0 Habc] := altP eqP.
  rewrite /coprimer !mulr0 add0r => Hbc.
  by rewrite (eqd_ltrans (gcd0r _)).
case: egcdrP => g u v a' b' Hab' Hg Hc Hr.
move: Hab' Hg =>  /(congr1 ( *%R^~ g)); rewrite mulrDl mul1r.
rewrite -!mulrA -Hc -Hr {Hc Hr} => <- {a' b' g}.
rewrite (eqd_rtrans (coprimer_gdco c an0)) => Hu.
have: 1 %| 1 - b by rewrite dvd1r.
rewrite -(eqd_dvdl _ Hu) /dvdr.
case: odivrP => //= k' /(canRL (addrNK _)).
rewrite mulrDr !mulrA addrAC !mul1r => Hk' _.
rewrite /coprimer; set d := gcdr _ _.
have cdc: coprimer d c.
  apply: gcdr_def; rewrite ?dvd1r // => t td tc.
  rewrite -(eqd_dvdr _ Habc) -addrA dvdr_add //.
    by rewrite dvdr_mull ?(dvdr_trans td) /d ?dvdr_gcdl.
  rewrite -[y * b](@addrNK _ (y * (b + k' * v * c))).
  rewrite {1}mulrDr opprD addrA subrr sub0r addrAC dvdr_add //; last first.
    by rewrite dvdr_mull // (dvdr_trans td) /d // dvdr_gcdr.
  by rewrite !mulrA addrC -mulrBl dvdr_mull.
suff dr: d %| gdco c a.
  by rewrite -dvdr1 Hk' -addrA dvdr_add // /d ?dvdr_gcdr // dvdr_mull.
case: gdcoP => /= [a_eq0|r a_neq0 ra crc]; first by rewrite a_eq0 eqxx in an0.
by apply => //; rewrite dvdr_gcdl.
Qed.

Definition gdco_smith := smithmxn (kap_smith gdco_kap).

Lemma gdco_smithP m n (M : 'M[R]_(m,n)) : smith_spec M (gdco_smith M).
Proof.
rewrite /gdco_smith.
by apply: smithmxnP; apply: kap_smithP; apply: gdco_kapP.
Qed.

Definition gdcoEDRMixin := EDR.Mixin gdco_smithP.
Canonical gdcoEDRType   := Eval hnf in EDRType R gdcoEDRMixin.

End AdequacyEDR.

Section BezoutKrull1.

Variable R : bezoutDomainType.

Implicit Types a b u : R.

Hypothesis krull1 : forall a u, exists m v, a %| u ^+ m * (1 - u * v).

Lemma krull1_factor a b :
  exists n b1 b2, [&& 0 < n, b == b1 * b2, coprimer b1 a & b2 %| a ^+ n].
Proof.
wlog suff: / exists n b1 b2,
             [&& 0 < n, b %= b1 * b2, coprimer b1 a & b2 %| a ^+ n].
  move=> [n [b1 [b2 /and4P [Hn Hb Hb1 Hb2]]]].
  have [b2_eq0|b2_neq0] := eqVneq b2 0.
    exists n, b1, b2; move: Hn Hb Hb1 Hb2.
    by rewrite b2_eq0 mulr0 eqdr0 => -> -> -> ->.
  have : b2 %| b by rewrite (eqd_dvdr _ Hb) dvdr_mull.
  case: dvdrP Hb => [[b1' ->]|//]; rewrite eqd_mul2r // => eq_b1'.
  exists n, b1', b2; rewrite !eqxx Hn Hb2 /coprimer andbT /=.
  by rewrite (eqd_ltrans (eqd_gcd eq_b1' (eqdd _))).
have kidem x : exists d (s : R) k,
  [&& 0 < d, b %| s ^+ 2 - s, b %| x ^+ d - (x ^+ d) * s
                               & b %| s - k * x ^+ d].
  have [m [y]] := krull1 b x.
  have [-> Hy|m_gt0 Hy] := posnP m.
    exists 1%N, 1, y; rewrite !expr1n mulr1 expr1 !subrr dvdr0 /=.
    by move: Hy; rewrite expr0 mul1r mulrC.
  set s := (x * y) ^+ m; exists m, s, (y ^+ m).
  have xsn n : b %| x ^+ m * (x * y) ^+ n - x ^+ m.
    elim: n => [|n ihn]; first by rewrite mulr1 subrr dvdr0.
    rewrite -[X in X - _](addrNK (x ^+ m * (x * y) ^+ n)) -addrA dvdr_add //.
    rewrite exprS mulrA -mulrBl dvdr_mulr //.
    by rewrite -dvdrN opprB -[X in X - _]mulr1 -mulrBr.
  have s_idem n : b %| s * (x * y) ^+ n - s.
    elim: n => [|n ihn]; first by rewrite mulr1 subrr dvdr0.
    rewrite -[X in X - _](addrNK (s * (x * y) ^+ n)) -addrA dvdr_add //.
    rewrite exprS mulrA -mulrBl dvdr_mulr //.
    rewrite /s -exprSr !exprMn exprSr exprS mulrA -mulrBl dvdr_mulr //.
    by rewrite -dvdrN opprB -{1}[x ^+ m]mulr1 -mulrA -mulrBr.
  rewrite m_gt0 (s_idem m) /= -opprB dvdrN (xsn m) /=.
  by rewrite mulrC -exprMn subrr dvdr0.
have [d [s [k /and4P [d_gt0 s_idem ads ska]]]] := kidem a.
set b1 := gcdr b (1 - s); set b2 := gcdr b s; exists d, b1, b2.
have dvd_b2_bd: b2 %| a ^+ d.
  rewrite -[a ^+ d](addrNK (a ^+ d * s)) dvdr_add ?andbT //=; last 2 first.
    by rewrite (dvdr_trans (dvdr_gcdl _ _)) //.
  by rewrite dvdr_mull // dvdr_gcdr.
have eq_b : b %= b1 * b2.
  rewrite eqd_def /b1 /b2.
  rewrite -[b as X in _ %| X](addrNK (b * s)).
  rewrite -[X in X - b * s]mulr1 -mulrBr dvdr_add ?andbT //=; last 2 first.
    by rewrite mulrC dvdr_mul // (dvdr_gcdl, dvdr_gcdr).
  by rewrite dvdr_mul // (dvdr_gcdl, dvdr_gcdr).
  have [[x y gbs] [x' y' gbs']] := (bezoutP b s, bezoutP b (1 - s)).
  rewrite (eqd_dvdr _ (eqd_mulr _ gbs')) (eqd_dvdr _ (eqd_mull _ gbs)).
  rewrite [1 - s]lock !(mulrDr, mulrDl) -!lock !addrA dvdr_add //=.
    by rewrite ![_ * b * _](mulrAC, mulrA) !mulrA -!mulrDl dvdr_mull.
  by rewrite mulrCA -mulrA dvdr_mull // dvdr_mull // mulrBl mul1r -opprB dvdrN.
rewrite dvd_b2_bd eq_b d_gt0 andbT //=.
have: coprimer b1 b2.
  apply: gcdr_def; rewrite ?dvd1r //= => p ps' ps.
  rewrite -[1](addrNK s) dvdr_add //.
    by rewrite (dvdr_trans ps') ?dvdr_gcdr.
  by rewrite (dvdr_trans ps) ?dvdr_gcdr.
have b2_eq : gcdr b s %= gcdr b (a ^+ d).
  rewrite eqd_def !dvdr_gcd !dvdr_gcdl /=.
  rewrite -[a ^+ d as X in _ %| X](addrNK ((a ^+ d) * s)).
  rewrite dvdr_add //=; last 2 first.
    by rewrite (dvdr_trans (dvdr_gcdl _ _)).
    by rewrite dvdr_mull ?dvdr_gcdr.
  rewrite -[s as X in _ %| X](addrNK (k * (a ^+ d))) dvdr_add //.
    by rewrite (dvdr_trans (dvdr_gcdl _ _)).
  by rewrite dvdr_mull ?dvdr_gcdr.
rewrite /b2 /coprimer (eqd_ltrans (eqd_gcd (eqdd _) b2_eq)).
rewrite (eqd_ltrans (gcdrA _ _ _)).
have gb1b: gcdr b1 b %= b1.
  rewrite eqd_def dvdr_gcdl dvdr_gcd dvdrr /=.
  by rewrite (eqd_dvdr _ eq_b) dvdr_mulr.
rewrite (eqd_ltrans (eqd_gcd gb1b (eqdd _))).
apply: coprimer_dvdr.
by rewrite -[d]prednK // exprS dvdr_mulr.
Qed.

Lemma krull1_adequate a b : { r : R & adequate_spec a b r }.
Proof.
have [] := eqVneq b 0; first by exists 0; constructor.
move: (krull1_factor a b) => factored.
have /sigW : (exists (x : nat * (R * R)),
      [&& 0 < x.1, b == x.2.1 * x.2.2, coprimer x.2.1 a & x.2.2 %| a ^+ x.1]).
  by case: factored => n [b1 [b2]]; exists (n,(b1,b2)).
case=> /= [[n [b1 b2]]] /= /and4P [ngt0 /eqP -> ca1b dvda2bn aneq0].
exists b1; constructor => /= [|||d] //; first by rewrite dvdr_mulr.
rewrite mulrC dvdr_mul2l ?unitd1 => [dvdda2|].
  apply: contra; rewrite -(@coprimer_pexpr _ n) //.
  apply: dvdr_coprime; exact: (dvdr_trans dvdda2 dvda2bn).
by apply: contraNneq aneq0 => ->; rewrite mul0r.
Qed.

Definition krull1_gdco a b := projT1 (krull1_adequate a b).

Lemma krull1_gdcoP a b : gdco_spec a b (krull1_gdco a b).
Proof.
rewrite /krull1_gdco; case: (krull1_adequate a b)=> r hr /=.
exact: adequate_gdco.
Qed.

Definition krull1_smith := gdco_smith krull1_gdco.

Lemma krull1_smithP m n (M : 'M[R]_(m,n)) : smith_spec M (krull1_smith M).
Proof. by apply: gdco_smithP=> a b; apply: krull1_gdcoP. Qed.

Definition krull1EDRMixin := EDR.Mixin krull1_smithP.
Canonical krull1EDRType   := Eval hnf in EDRType R krull1EDRMixin.

End BezoutKrull1.

Section AdequacyPID.

Variable R : pidType.

Implicit Types a b : R.

Lemma pid_gdco a b : {r : R & gdco_spec a b r}.
Proof.
have [->|b_neq0] := eqVneq b 0; first by exists 0; constructor.
elim: (sdvdr_wf b) => {b} b _ ihp in b_neq0 *.
have [cba|ncba] := boolP (coprimer a b).
  by exists b; constructor; rewrite ?cpa ?orbT // coprimer_sym.
have := dvdr_gcdr a b; case: dvdrP => // [/choice.sig_eqW /= [r b_eq _]].
have := b_neq0; rewrite b_eq mulf_eq0 negb_or => /andP [r_neq0 g_neq0].
have [||r' r_gdco] // := ihp r.
  by rewrite sdvdr_def b_eq dvdr_mulr //= dvdr_mull_l.
case: r_gdco r_neq0 => [->|/= {r'} r' _ dvdr'r cr'q r'P r_neq0].
  by rewrite eqxx.
exists r'; constructor; rewrite ?dvdr_mulr // -?b_eq //=.
move=> d dp cdq; apply: r'P => //.
rewrite -(@euclid _ (gcdr a b)) -?b_eq //.
exact: coprimer_dvdr (dvdr_gcdl _ _) _.
Qed.

Definition pid_smith := gdco_smith (fun a b => projT1 (pid_gdco a b)).

Lemma pid_smithP m n (M : 'M[R]_(m,n)) : smith_spec M (pid_smith M).
Proof.
by rewrite /pid_smith; apply: gdco_smithP=> a b; case: (pid_gdco a b).
Qed.

Definition pidEDRMixin := EDR.Mixin pid_smithP.
Canonical pidEDRType   := Eval hnf in EDRType R pidEDRMixin.

(* This should be provable *)
(* Lemma pri_krull1 (a : R) (u : R) : exists m v, a %| u ^+ m * (1 - u * v). *)
(* Proof. *)
(* admit. *)
(* Qed. *)

End AdequacyPID.
