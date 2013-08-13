Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import mxalgebra perm zmodp matrix ssrint refinements funperm seqmatrix.

Section generic_Gaussian_elim.

Variable A : Type.

Import Refinements.Op.

Variable mxA : nat -> nat -> Type.
Variable ordA : nat -> Type.
Variable permA : nat -> Type.
Variable find_pivot : forall m n, mxA m.+1 n.+1 -> option (ordA (1 + m)).

Context `{zero A, one A, inv A, forall m n, scale A (mxA m n)}.
Context `{!hadd mxA, !hsub mxA, !hmul mxA, !hcast mxA}.
Context `{!ulsub mxA, !ursub mxA, !dlsub mxA, !drsub mxA, !block mxA}.

Context `{forall m, zero (ordA (1 + m))}.
Context `{forall m, zero (ordA m.+1)}.
Context `{xrow_class ordA mxA, row_perm_class permA mxA}.
Context `{forall n, tperm_class (ordA n) (permA n)}.
Context `{fun_of A ordA mxA, scalar_mx_class A mxA, lift0_perm_class permA}.
Context `{forall n, mul (permA n)}.
Context `{forall n, one (permA n)}.
Context `{const_mx_class A mxA}.

Arguments find_pivot {m n} _.

Open Scope hetero_computable_scope.
Open Scope computable_scope.

Notation "''M_' ( m , n )" := (mxA m n) : type_scope.
Notation "''M_' n" := (mxA n n) : type_scope.
Notation "''S_' n" := (permA n) : type_scope.

Fixpoint cormen_lup {m n} :=
  match m, n return 'M_(m.+1,n.+1) -> 'S_m.+1 * 'M_(m.+1,m.+1) * 'M_(m.+1,n.+1) with
  | p.+1, _.+1 => fun (A : 'M_(1 + (1 + p), 1 + _)) =>
    let k := odflt 0 (find_pivot A) in
    let A1 : 'M_(1 + _, 1 + _) := xrow 0 k A in
    let P1 : 'S_(1 + (1 + p)) := tperm 0 k in
    let Schur := ((fun_of_matrix A k 0)^-1 *: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur)%HC in
    let P := (lift0_perm P2) * P1 in
    let pA1 := row_perm P2 (dlsubmx A1) in
    let L := block_mx 1%:M (const_mx 0) ((fun_of_matrix A k 0)^-1 *: pA1) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) (const_mx 0) U2 in
    (P, L, U)
  | _, _ => fun A => (1, 1%:M, A)
  end.

End generic_Gaussian_elim.

Section Gaussian_correctness.

Import Refinements.Op.
Import GRing.Theory.

Local Open Scope ring_scope.

Variable F : fieldType.

Instance : zero F := 0%R.
Instance : one F := 1%R.
Instance : inv F := GRing.inv.
Instance : forall m n, scale F 'M[F]_(m,n) := fun m n => (@GRing.scale _ _).

Instance : hadd (matrix F) := @addmx F.
Instance : hsub (matrix F) := (fun _ _ M N => M - N).
Instance : hmul (matrix F) := @mulmx F.
Instance : hcast (matrix F) := @matrix.castmx F.
Instance : ulsub (matrix F) := @matrix.ulsubmx F.
Instance : ursub (matrix F) := @matrix.ursubmx F.
Instance : dlsub (matrix F) := @matrix.dlsubmx F.
Instance : drsub (matrix F) := @matrix.drsubmx F.
Instance : block (matrix F) := @matrix.block_mx F.
Instance : xrow_class ordinal (matrix F) := @matrix.xrow F.
Instance : forall n, tperm_class 'I_n 'S_n :=
  fun n => perm.tperm : 'I_n -> 'I_n -> 'S_n.
Instance : forall n, mul 'S_n := fun n => @perm_mul _.
Instance : lift0_perm_class (fun n => 'S_n) := @matrix.lift0_perm.
Instance : fun_of F ordinal (matrix F) := @matrix.fun_of_matrix F.
Instance : forall n, one 'S_n := fun n => 1%g.
Instance : scalar_mx_class F (matrix F) := @matrix.scalar_mx F.
Instance : const_mx_class F (matrix F) := @matrix.const_mx F.
Instance : row_perm_class (fun n => 'S_n) (matrix F) := @matrix.row_perm F.
Instance : forall n, zero 'I_(1 + n) := fun n => 0%R.
Instance : forall n, zero 'I_n.+1 := fun n => 0%R.

Definition f : forall m n, 'M[F]_(m.+1,n.+1) -> option 'I_(1 + m) :=
  fun m n A => [pick k | A k 0 != 0].

Definition cormen_lupF {m n} (M : 'M_(m.+1,n.+1)) :=
  cormen_lup F (matrix F) ordinal (fun n => 'S_n) f M.

Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lupF A in matrix.row_perm P A = L * U.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite row_perm1 mul1r.
simpC.
rewrite /row_perm /row_perm_class_instance_0.
(* Why do we have to do this ? *)
rewrite /hsub_op /hsub_instance_0.
rewrite /block_mx /block_instance_0.
(*********)
set k := odflt _ _; set A1 : 'M_(1 + _) := matrix.xrow _ _ _.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lupF => [[P' L' U']] /= IHn.
(* glueing code *)
rewrite row_permM !row_permE.
rewrite -lift0_mx_perm.
rewrite /lift0_mx.
(****************)
rewrite -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
rewrite row_permE /scale_op /scale_instance_0.
rewrite /inv_op /inv_instance_0.
rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulrDr {A'}subrK.
congr (matrix.block_mx _ _ (_ *m _) _).
rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.
rewrite /f.
case: pickP => /= [k nzAk0 | no_k]; first by rewrite mulVf ?mulmx1.
rewrite (_ : matrix.dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
by rewrite !mxE lshift0 (elimNf eqP (no_k _)).
Qed.

Lemma cormen_lup_detL n (A : 'M_n.+1) : \det (cormen_lupF A).1.2 = 1.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite det1.
simpC.
rewrite /hsub_op /hsub_instance_0.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lupF => [[P L U]] {A'}/= detL.
by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

Lemma cormen_lup_lower n (A : 'M_n.+1) (i j : 'I_n.+1) :
  i <= j -> (cormen_lupF A).1.2 i j = (i == j)%:R.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1 [j]ord1 mxE.
simpC.
rewrite /hsub_op /hsub_instance_0.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lupF => [[P L U]] {A'}/= Ll.
rewrite !mxE split1; case: unliftP => [i'|] -> /=; rewrite !mxE split1.
  by case: unliftP => [j'|] -> //; exact: Ll.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma cormen_lup_upper n A (i j : 'I_n.+1) :
  j < i -> (cormen_lupF A).2 i j = 0 :> F.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1.
simpC.
rewrite /hsub_op /hsub_instance_0.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lupF => [[P L U]] {A'}/= Uu.
rewrite !mxE split1; case: unliftP => [i'|] -> //=; rewrite !mxE split1.
by case: unliftP => [j'|] ->; [exact: Uu | rewrite /= mxE].
Qed.

End Gaussian_correctness.

Section Gaussian_elim_seqmx.

Variable A : Type.

Import Refinements.Op.

Context `{zero A, one A, add A, sub A, mul A, inv A, eq A}.

Fixpoint find_pivot_seqmx j (r : seqmatrix A) {struct r} : option nat :=
  if r is x::r' then
    if (head 0 x == 0)%C then find_pivot_seqmx j.+1 r' else Some j
  else None.

Definition hseqmatrix := fun _ _ : nat => seqmatrix A.
Definition natord := fun _ : nat => nat.

Instance : forall n, zero (natord n) := fun _ => 0.

Instance : xrow_class natord hseqmatrix :=
  fun _ _ => @xrowseqmx A.

Instance : row_perm_class (fun _ => funperm) hseqmatrix :=
  fun m n => @row_perm_seqmx A m.

Instance : forall n, tperm_class (natord n) funperm :=
  fun n => ctperm.

Instance : fun_of A natord hseqmatrix :=
  fun _ _ M i j => nth 0%C (nth [::] M i) j.

Instance : scalar_mx_class A hseqmatrix :=
  @scalar_seqmx A _.

Instance : lift0_perm_class (fun _ => funperm) :=
  fun _ => lift0_cperm.

Instance : forall n : nat, mul funperm :=
  fun _ => cperm_comp.

Instance : forall n : nat, one funperm :=
  fun _ => id.

Instance : const_mx_class A hseqmatrix :=
  @const_seqmx A.

Definition cormen_lup_seqmx (m n : nat) (M : seqmatrix A) := cormen_lup A (m := m) (n := n) (fun _ _ => seqmatrix A) (fun _ => nat) (fun _ => funperm) (fun _ _ => find_pivot_seqmx 0) M.

(*
Fixpoint cormen_lup_seqmx m n :=
  match m, n return let M := seqmatrix A in M -> (nat -> nat) * M * M with
  | p.+1, q.+1 => fun A =>
    let k := odflt 0 (find_pivot_seqmx 0 A) in
    let A1 := xrowseqmx 0 k A in
    let P1 := ctperm 0 k in
    let a := (nth 0 (nth [::] A k) 0)^-1%C in
    let Schur := mulseqmx 1 q (scaleseqmx a (dlsubseqmx 1 1 A1))%C (ursubseqmx 1 1 A1) in
    let: (P2, L2, U2) := cormen_lup_seqmx p q (drsubseqmx 1 1 A1 - Schur)%C in
    let P := cperm_comp (lift0_cperm P2) P1 in
    let pA1 := row_perm_seqmx p P (dlsubseqmx 1 1 A1) in
    let L := block_seqmx (scalar_seqmx 1 1%C) (const_seqmx 1 q 0%C) (scaleseqmx a pA1) L2 in
    let U := block_seqmx (ulsubseqmx 1 1 A1) (ursubseqmx 1 1 A1) (const_seqmx p 1 0%C) U2 in
    (P, L, U)
  | _, _ => fun A => (id, scalar_seqmx 1 1%C, A)
  end.
*)

End Gaussian_elim_seqmx.

Require Import Int31 intmodp.

Section bench_modular.

Open Scope int31_scope.

Definition test : seqmatrix int :=
[::[::690;556;422;654;425;281;168;498;599;950];
[::310;847;143;689;803;759;756;495;683;887];
[::208;266;777;214;448;111;262;275;155;198];
[::391;971;366;980;433;321;941;290;831;717];
[::117;312;978;612;270;812;571;980;501;432];
[::548;929;906;192;246;966;516;461;956;816];
[::742;295;642;315;209;815;849;438;558;821];
[::616;425;889;412;173;881;994;641;128;389];
[::252;838;677;255;709;909;726;735;33;729];
[::109;396;461;863;240;397;409;120;998;990]].

Definition res := cormen_lup_seqmx int 9 9 test.

Eval native_compute in ignore res.

Definition res_test := eq_seqmx (m := 10%nat) (n := 10%nat) (row_perm_seqmx 10 res.1.1 test) (mulseqmx (m := 10%nat) (n := 10%nat) (p := 10%nat) res.1.2 res.2).

Eval native_compute in res_test.

End bench_modular.

(*
Section bench.

Local Open Scope bigQ_scope.

Definition test : seqmatrix bigQ :=
[::[::690;556;422;654;425;281;168;498;599;950];
[::310;847;143;689;803;759;756;495;683;887];
[::208;266;777;214;448;111;262;275;155;198];
[::391;971;366;980;433;321;941;290;831;717];
[::117;312;978;612;270;812;571;980;501;432];
[::548;929;906;192;246;966;516;461;956;816];
[::742;295;642;315;209;815;849;438;558;821];
[::616;425;889;412;173;881;994;641;128;389];
[::252;838;677;255;709;909;726;735;33;729];
[::109;396;461;863;240;397;409;120;998;990]].

(*
Time Eval vm_compute in (fun _ => true) test.
*)

Definition res := cormen_lup_seqmx bigQ 9 9 test.

Definition check := BigQ.eqb (nth 0 (nth [::] res.2 5) 5) (171161476272805220 # 45087845519841).

Eval vm_compute in eq_seqmx (row_perm_seqmx 10 res.1.1 test) (mulseqmx 10 10 res.1.2 res.2).

Eval vm_compute in check.

(*
Time Eval vm_compute in (fun _ => true) res.
*)

(*
Time Eval vm_compute in (fun _ => true) test2.
*)

End bench.

(*
Time Eval vm_compute in (fun _ => true) res2.


Definition test n := mkseqmx_ord (fun (i j : 'I_n) => odd (i + j)).

Definition n := 70.

Definition test0 := test n.

Time Eval vm_compute in (fun _ => true) test0.

Definition res := cormen_lup_seqmx bool n n test0.

Local Notation "0" := false.
Local Notation "1" := true.

Time Eval vm_compute in row_perm_seqmx n res.1.1 test0.
Time Eval vm_compute in mulseqmx n n res.1.2 res.2.


Time Eval vm_compute in (fun _ => true) res.

Fixpoint Gaussian_elim {m n} : 'M[F]_(m, n) -> 'M[F]_m * 'M[F]_n * nat :=
  match m, n with
  | k.+1, l.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if f k l A is Some (i, j) then
      let a := A i j in let A1 := xrow i 0 (xcol j 0 A) in
      let u := ursubmx A1 in let v := a^-1 *: dlsubmx A1 in
      let: (L, U, r) := Gaussian_elim (drsubmx A1 - v *m u) in
      (xrow i 0 (block_mx 1 0 v L), xcol j 0 (block_mx a%:M u 0 U), r.+1)
    else (1%:M, 1%:M, 0%N)
  | _, _ => fun _ => (1%:M, 1%:M, 0%N)
  end.

Lemma gaussian_elimP m n (M N : 'M_(m,n)) :
  (forall m n (A : 'M[R]_(1 + m,1 + n)), pick_spec [pred ij | A ij.1 ij.2 != 0] (f m n A)) ->
  (M :=: N)%MS ->
  let:(L,U,r) := Gaussian_elimination M in
  let:(L',U',r') := Gaussian_elim N in
  (U :=: U')%MS /\ r = r'.
Proof.
move=> pick_F.
elim: m n M N => // m IHm.
case=> // n M N eqmx_MN /=.
have [[i j] /= Hij|] := pickP.
have [[i' j'] /= Hi'j'|] := pick_F; last first.
move=> eq_N0F.
have eq_N0: N = 0.
apply/matrixP=> k l.
rewrite !mxE.
by rewrite (eqP (negbFE (eq_N0F (k,l)))).
rewrite eq_N0 in eqmx_MN.
move: Hij.
move:(eqmx_eq0 eqmx_MN); rewrite eqxx.
move/eqP=> ->.
by rewrite mxE eqxx.
set M' := (drsubmx (xrow i 0 (xcol j 0 M)) -
                (M i j)^-1 *: dlsubmx (xrow i 0 (xcol j 0 M)) *m 
                ursubmx (xrow i 0 (xcol j 0 M))).
set N' :=  (drsubmx (xrow i' 0 (xcol j' 0 N)) -
                     (N i' j')^-1 *: dlsubmx (xrow i' 0 (xcol j' 0 N)) *m 
                     ursubmx (xrow i' 0 (xcol j' 0 N))).
move: (IHm _ M' N').
case: (Gaussian_elimination M') => [[L U] r].
case: (Gaussian_elim N') => [[L' U'] r'].




























move=> H; elim: m M=> // m.
case:n=> // n IHm M.
rewrite /=.
case:(H _ _ M)=> [[i j] /= Hij| eq_M0]; case:pickP=> [[i' j'] /= Hij'| // eq_M0].
+
set M' := (drsubmx (xrow i' 0 (xcol j' 0 M)) -
                (M i' j')^-1 *: dlsubmx (xrow i' 0 (xcol j' 0 M)) *m 
                ursubmx (xrow i' 0 (xcol j' 0 M))).

move:(IHm _).

+ by rewrite (eq_M0 (i,j)) in Hij.
by move:(eq_M0 (i',j')) Hij' => /= ->.
Qed.

set M' :=  (drsubmx (xrow i 0 (xcol j 0 M)) -
                        (M i j)^-1 *: dlsubmx (xrow i 0 (xcol j 0 M)) *m 
                        ursubmx (xrow i 0 (xcol j 0 M))).
case H: (Gaussian_elimination _).
set M' := (Gaussian_elimination _).
move:(IHm ).


Fixpoint gaussian_elimination {m n} (f : pred 'I_m.+1 * 'I_n.+1 -> option 'I_m.+1 * 'I_n.+1) : 'M_(m.+1, n.+1) -> 'M_m.+1 * 'M_n.+1 * nat :=
  match m, n with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if f [pred ij | A ij.1 ij.2 != 0] is Some (i, j) then
      let a := A i j in let A1 := xrow i 0 (xcol j 0 A) in
      let u := ursubmx A1 in let v := a^-1 *: dlsubmx A1 in
      let: (L, U, r) := gaussian_elimination f (drsubmx A1 - v *m u) in
      (xrow i 0 (block_mx 1 0 v L), xcol j 0 (block_mx a%:M u 0 U), r.+1)
    else (1%:M, 1%:M, 0%N)
  | _, _ => fun _ => (1%:M, 1%:M, 0%N)
  end.

Fixpoint find_pivot {m n} (M : 'M[R]_(m.+1, n.+1)) i : option (nat * R) :=
  if i is i'.+1 then
    if M (inord i') 0 != 0 then Some (i', M (inord i') 0) else find_pivot M i'
  else None.

Lemma find_pivotP : 


Fixpoint find_pivot_seq (M : seqmatrix R) i {struct i} : option (nat * R) :=
  if i is i'.+1 then
    if M is s::M' then
      if nth 0 s 0 != 0 then Some (i', nth 0 s 0) else find_pivot_seq M' i'
    else None
  else None.

Lemma find_pivot_seqE (m n : nat) (M : 'M[R]_(m.+1, n.+1)) : forall i,
  find_pivot_seq (seqmx_of_mx M) i = find_pivot M i.
Proof.
admit.
(*
elim=> // i.
move:(@size_row_seqmx _ _ _ M 0 (erefl _)); move:(seqmxE M 0 0); move:(size_seqmx M).
case:(seqmx_of_mx M)=> // t s _.
case:t=> // a s'.
rewrite /fun_of_seqmx /==> -> _.


  move/eqP; rewrite eqSS; move/eqP=> Hs.
  rewrite (size0nil Hs).

  rewrite /fun_of_seqmx /==> -> _.
  by rewrite -[0]inord_val.
rewrite /=.

  move=> n M; move:(@size_row_seqmx _ _ _ M 0 (erefl _)); move:(seqmxE M 0 0); move:(size_seqmx M).
  case (seqmx_of_mx M)=> // t s.
  move/eqP; rewrite eqSS; move/eqP=> Hs.
  rewrite (size0nil Hs).
  case:t=> // a s'.
  rewrite /fun_of_seqmx /==> -> _.
  by rewrite -[0]inord_val.
move=> m IHm n M.
move:(seqmxE M 0 0); move:(size_seqmx M).
(*
move:(@size_row_seqmx _ _ _ M 0 (erefl _)); 
*)
move:(IHm _ M).
case (seqmx_of_mx M)=> // t s.
*)
Qed.

Print pick_spec.

Fixpoint gauss {m n} : 'M[R]_(m, n) -> 'M[R]_m * 'M[R]_n * nat :=
  match m, n return 'M_(m, n) -> 'M_m * 'M_n * nat with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if find_pivot A m is Some (i, a) then
      let A1 : 'M_(1 + _, 1 + _) := xrow i 0 A in
      let u := ursubmx A1 in let v := a^-1 *: dlsubmx A1 in
      let: (L, U, r) := gauss (drsubmx A1 - v *m u) in
      (xrow i 0 (block_mx 1 0 v L), block_mx a%:M u 0 U, r.+1)
    else (1%:M, 1%:M, 0%N)
  | _, _ => fun _ => (1%:M, 1%:M, 0%N)
  end.

Lemma gaussP (m n : nat) (M : 'M[R]_(m.+1, n.+1)) :
  let:(L,U,r) := gaussian_elimination M in
  let:(_,U',r') := gauss M in
  (U :=: U')%MS /\ r = r'.
Proof.
Admitted.

Fixpoint gaussseqmx m n : seqmatrix R -> seqmatrix R :=
  match m, n return seqmatrix R -> seqmatrix R with
  | m'.+1, n'.+1 => fun A : seqmatrix R =>
    if find_pivot_seq A m is Some (i,a) then
      let A1 := xrowseqmx 0 i A in
      let u := ursubseqmx 1 1 A1 in
      let v := scaleseqmx a^-1 (dlsubseqmx 1 1 A1) in
      let U := (subseqmx (drsubseqmx 1 1 A1) (mulseqmx v u)) in
      let U := gaussseqmx m' n' U in
      (block_seqmx [::[::a]] u (nseq n' [::0]) U)
    else let: U := gaussseqmx m' n' (drsubseqmx 1 1 A) in
    let u := ursubseqmx 1 1 A in
    block_seqmx [::[::0]] u (nseq n' [::0]) U
  | _, _ => fun _ => [::]
  end.

End gaussian_elimination.

Local Open Scope ring_scope.

Definition M2 :=
  [::[::2%:Q;1%:Q];
  [::1%:Q;2%:Q]].

Eval native_compute in gaussseqmx _ 2 2 M2.

Definition M1 :=
  [:: [::0%:Q;1%:Q;2%:Q];
  [::0%:Q;2%:Q;1%:Q];
  [::2%:Q;1%:Q;1%:Q]].

Eval compute in gaussseqmx _ 3 3 M1.*)
*)