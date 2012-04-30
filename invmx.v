Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix ssrcomplements.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section invmx.

Import GRing.Theory.
Local Open Scope ring_scope.

Variable R : comUnitRingType.

Lemma invmx_left : forall m (M M' : 'M[R]_m), M *m M' = 1%:M -> M' *m M = 1%:M.
Proof.
move=> m M M' H.
have hM : (M \in unitmx) by case: (mulmx1_unit H).
have h' : (M' = invmx M) by rewrite -(mulKmx hM M') H mulmx1.
by rewrite h' mulVmx.
Qed.

Lemma invmx_uniq m (M M' : 'M[R]_m) :
  M *m M' = 1%:M -> M' = invmx M.
Proof.
move=> H.
have hM : (M \in unitmx) by case: (mulmx1_unit H).
by rewrite -[M']mulmx1 -(mulmxV hM) mulmxA (invmx_left H) mul1mx.
Qed.


Fixpoint fast_invmx (m : nat) : 'M[R]_m -> 'M[R]_m :=
  match m return 'M[R]_m -> 'M[R]_m with
  | S p => fun (M : 'M[R]_(1 + p)) =>
           let: N := fast_invmx (drsubmx M) in
           block_mx 1%:M 0 (- N *m dlsubmx M) N
  | O => fun _ => 1%:M
  end.

Definition lower1 m (M : 'M[R]_m) :=
  forall (i j : 'I_m), i <= j -> M i j = (i == j)%:R.

Lemma drlower1 : forall m (M : 'M[R]_(1 + m)%N),
  lower1 M -> lower1 (drsubmx M).
Proof.
move=> m M H i j hij.
by rewrite !mxE !rshift1 H.
Qed.

Lemma urlower1 : forall m (M : 'M[R]_(1 + m)%N),
  lower1 M -> ursubmx M = 0.
Proof.
move=> m M H.
apply/rowP => i.
by rewrite !mxE lshift0 rshift1 H.
Qed.

Lemma ullower1 : forall m (M : 'M[R]_(1 + m)%N),
  lower1 M -> ulsubmx M = 1%:M.
Proof.
move=> m M H.
apply/rowP=> i.
by rewrite !mxE !ord1 H.
Qed.

Lemma fast_invmxE : forall m (M : 'M[R]_m),
  lower1 M -> M *m fast_invmx M = 1%:M.
Proof.
elim=> [M |n ih]; first by rewrite !thinmx0.
rewrite [n.+1]/(1 + n)%N => M hM /=.
rewrite -{1}[M]submxK (@mulmx_block _ 1 n 1 n 1 n).
rewrite !mulmx0 !mulmx1 !add0r ih; last by apply/drlower1.
rewrite (urlower1 hM) !mul0mx addr0 mulmxA mulmxN ih; last by apply/drlower1.
by rewrite mulNmx mul1mx subrr ullower1 -?scalar_mx_block.
Qed.

Lemma fast_invmxP m (M : 'M[R]_m) (H : lower1 M) :
  fast_invmx M = invmx M.
Proof.
apply/invmx_uniq.
by rewrite fast_invmxE.
Qed.

End invmx.

(*
Extraction Language Haskell.
Extraction fast_invmx.
*)

Section seqinvmx.

Require Import cssralg seqmatrix.

Variable R : comUnitRingType.
Variable CR : cunitRingType R.

Fixpoint cfast_invmx (m : nat) (M : seqmatrix CR) :=
  match m with
  | S p =>
   let: N := cfast_invmx p (drsubseqmx 1 1 M) in
   block_seqmx (seqmx1 _ 1) (seqmx0 _ 1 p)
               (mulseqmx (oppseqmx N) (dlsubseqmx 1 1 M)) N
  | O => seqmx1 _ O
  end.

Lemma cfast_invmxP : forall (m : nat),
  {morph (@seqmx_of_mx _ CR m m) : M / fast_invmx M >-> cfast_invmx m M}.
Proof.
elim=> [M|m ih]; first by rewrite seqmx1E.
rewrite [m.+1]/(1 + m)%N => M /=.
rewrite -(@block_seqmxE _ _ 1 _ 1) seqmx1E seqmx0E ih -drsubseqmxE; f_equal.
(* Ask Maxime to fix mulseqmxE! *)
have -> : seqmx_of_mx CR (- fast_invmx (drsubmx M) *m dlsubmx M) =
          mulseqmx (seqmx_of_mx CR (- fast_invmx (drsubmx M))) (seqmx_of_mx CR (dlsubmx M)).
  clear ih.
  case: m M => [|n] M; last by rewrite mulseqmxE.
    by rewrite !thinmx0 mul0mx flatmx0 !seqmx0E /=.
by rewrite oppseqmxE ih -drsubseqmxE -dlsubseqmxE.
Qed.

End seqinvmx.

(*
Extraction Language Haskell.
Extract Inductive seq => "list" [ "[]" "(::)" ].
Extraction cfast_invmx.
Recursive Extraction cfast_invmx.
*)

(* Benchmark
Require Import ZArith.
Require Import Zinfra.

Time Eval vm_compute in
  cfast_invmx 3 [:: [:: 1%Z; 0%Z; 0%Z]; [:: 0%Z; 1%Z; 0%Z]; [:: 0%Z; 0%Z; 1%Z]].

Time Eval vm_compute in
  cfast_invmx 3 [:: [:: 1%Z; 0%Z; 0%Z]; [:: 2%Z; 1%Z; 0%Z]; [:: 5%Z; 1%Z; 1%Z]].

Definition mat n := (1%Z :: nseq (n-1) 0%Z) :: [seq map Z_of_nat ((take x (iota x n)) ++ 1 :: nseq (n-x) 0) | x <- iota 1 n].

Eval vm_compute in mat 10.

Definition m15 := Eval vm_compute in (mat 15).
Time Eval vm_compute in m15.

Time Eval vm_compute in (cfast_invmx 16 m15).

Time Eval vm_compute in (cfast_invmx 11 (mat 10)).

Require Import boolF2.

Definition tobool := map (map Zodd_bool).

Time Eval vm_compute in (tobool m15).
Definition b15 := Eval vm_compute in tobool m15.
Time Eval vm_compute in mulseqmx b15 (cfast_invmx 16 b15).
*)

(* Compare with naïve implementation *)
Section determinant.

Variable R' : comRingType.
Variable R : cringType R'.

Fixpoint expand sign (mat : seqmatrix R) det acc : R :=
  if mat is a :: tl then
    add (mul sign (mul (head (zero R) a) (det (rev acc ++ (map behead tl)))))
        (expand (opp sign) tl det (behead a :: acc))
  else zero R.

Fixpoint det_seqmx n (mat : seqmatrix R) : R :=
  if n is p.+1 then expand (one R) mat (det_seqmx p) [::] else one R.


Definition czip (v:seq R) (l: seq (seq R)) :=
  map (fun p => let: (x,y) := p in x::y) (zip v l).


End determinant.

Section invmxseq.

Variable R' : comUnitRingType.
Variable R : cunitRingType R'.

Section definitions.

Definition splice_out i (A : seq R) := (take i A) ++ drop (i+1) A.

(* A with the i'th row spliced out.*)
Definition row'_seqmx i (A:seqmatrix R) :seqmatrix R := (take i A) ++ drop (i+1) A.

(* A with the j'th column spliced out.*)
Definition col'_seqmx j (A:seqmatrix R) :seqmatrix R := map (splice_out j) A.

(* the i, j cofactor of A (the signed i, j minor of A *)
Definition cofactor_seqmx n (A:seqmatrix R) i j :=
  if odd (i + j) then opp (det_seqmx n.-1 (row'_seqmx i (col'_seqmx j A)))
                 else  (det_seqmx n.-1 (row'_seqmx i (col'_seqmx j A))).

(* The adjugate matrix : defined as the transpose of the matrix of cofactors *)
Definition adjugate_seqmx n (A:seqmatrix R) :=
  map (fun i => map (fun j => (cofactor_seqmx n A j i)) (iota 0 n)) (iota 0 n).

Definition invmx_seqmx n (A:seqmatrix R) :=
  if (cunit (det_seqmx n A)) then (scaleseqmx (cinv (det_seqmx n A)) (adjugate_seqmx n A)) else A.

End definitions.

End invmxseq.

(* OMG at 7 it breaks!
Time Eval vm_compute in invmx_seqmx 6 (tobool (mat 5)).
Time Eval vm_compute in cfast_invmx 6 (tobool (mat 5).
Time Eval vm_compute in invmx_seqmx 16 b15.
*)