Require Import BigQ.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import mxalgebra perm zmodp matrix ssrint refinements cperm seqmatrix.
Require Import boolF2 bigQrat.

Section generic_Gaussian_elim.

Variable A : Type.

Import Refinements.Op.

Variable mxA : nat -> nat -> Type.
Variable ordA : nat -> Type.
Variable permA : nat -> Type.
Variable f : forall m n, mxA m.+1 n.+1 -> option (ordA (1 + m)).

Variable xrow : forall m n, ordA m -> ordA m -> mxA m n -> mxA m n.
Variable tperm : forall n, ordA n -> ordA n -> permA n.
Variable perm_comp : forall n, permA n -> permA n -> permA n.
Variable lift0_perm : forall n, permA n -> permA n.+1.
Variable getmxA : forall m n, mxA m n -> ordA m -> ordA n -> A.
Variable perm1 : forall n, permA n.
Variable scalar_mx : forall n, A -> mxA n n.
Variable const_mx : forall m n, A -> mxA m n.
Variable row_perm : forall m n, permA m -> mxA m n -> mxA m n.
Variable ord0 : forall n, ordA n.+1.

Context `{zero A, one A, inv A, forall m n, scale A (mxA m n)}.
Context `{!hadd mxA, !hsub mxA, !hmul mxA, !hcast mxA}.
Context `{!ulsub mxA, !ursub mxA, !dlsub mxA, !drsub mxA, !block mxA}.

Arguments xrow {m n} _ _ _.
Arguments tperm {n} _ _.
Arguments perm_comp {n} _ _.
Arguments lift0_perm {n} _.
Arguments getmxA {m n} _ _ _.
Arguments perm1 {n}.
Arguments row_perm {m n} _ _.

Open Scope computable_scope.

Fixpoint cormen_lup {m n} :=
  match m, n return mxA m.+1 n.+1 -> permA m.+1 * mxA m.+1 m.+1 * mxA m.+1 n.+1 with
  | _.+1, _.+1 => fun A =>
    let k := odflt (ord0 _) (f _ _ A) in
    let A1 : mxA (1 + _) (1 + _) := xrow (ord0 _) k A in
    let P1 : permA (1 + _) := tperm (ord0 _) k in
    let Schur := hmul_op ((getmxA A k (ord0 _))^-1 *: dlsub_op A1) (ursub_op A1) in
    let: (P2, L2, U2) := cormen_lup (hsub_op (drsub_op A1) Schur) in
    let P := perm_comp (lift0_perm P2) P1 in
    let pA1 := row_perm P2 (dlsub_op A1) in
    let L := block_op (scalar_mx 1%N 1%C) (const_mx _ _ 0%C) ((getmxA A k (ord0 _))^-1 *: pA1) L2 in
    let U := block_op (ulsub_op A1) (ursub_op A1) (const_mx _ _ 0%C) U2 in
    (P, L, U)
  | _, _ => fun A => (perm1, scalar_mx _ 1%C, A)
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
Instance : hcast (matrix F) := @castmx F.
Instance : ulsub (matrix F) := @ulsubmx F.
Instance : ursub (matrix F) := @ursubmx F.
Instance : dlsub (matrix F) := @dlsubmx F.
Instance : drsub (matrix F) := @drsubmx F.
Instance : block (matrix F) := @block_mx F.

Definition f : forall m n, 'M[F]_(m.+1,n.+1) -> option 'I_(1 + m) :=
  fun m n A => [pick k | A k 0 != 0].

Definition cormen_lupF {m n} (M : 'M_(m.+1,n.+1)) := cormen_lup F (matrix F) ordinal (fun n => 'S_n) f (@xrow F) (fun n => tperm) (fun n => @perm_mul _) lift0_perm (@fun_of_matrix F) (fun n => perm_one _) (@scalar_mx _) (@const_mx _) (@row_perm _) (@ord0) M.

Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lupF A in row_perm P A = L * U.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite row_perm1 mul1r.
simpC.
(* Why do we have to do this ? *)
rewrite /hsub_op /hsub_instance_0.
rewrite /block_op /block_instance_0.
(*********)
set k := odflt _ _; set A1 : 'M_(1 + _) := xrow _ _ _.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lupF => [[P' L' U']] /= IHn.
(* glueing code *)
rewrite row_permM !row_permE.
rewrite -lift0_mx_perm.
rewrite /lift0_mx.
(****************)
rewrite -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
rewrite row_permE /scale_op /scale_instance_0.
rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulrDr {A'}subrK.
congr (block_mx _ _ (_ *m _) _).
rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.
rewrite /f.
case: pickP => /= [k nzAk0 | no_k]; first by rewrite mulVf ?mulmx1.
rewrite (_ : dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
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

Definition cormen_lup_seqmx (m n : nat) (M : seqmatrix A) := cormen_lup A (hseqmatrix A) (fun _ => nat) (fun n => nat -> nat) (fun _ _ => find_pivot_seqmx 0) (fun _ _ => @xrowseqmx A) (fun _ => ctperm) (fun _ => cperm_comp) (fun _ => lift0_cperm) (fun _ _ A i j => nth 0%C (nth [::] A i) j) (fun n => id) (fun n => scalar_seqmx n) (fun m n => const_seqmx m n) (fun m _ => row_perm_seqmx m) (fun _ => 0%N) (m := m) (n := n) M.

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