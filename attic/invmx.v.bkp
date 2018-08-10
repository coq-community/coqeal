(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import Numbers.BinNums.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp Require Import perm zmodp matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* Inverting triangular matrices (with 1:s on the diagonal) *)
Section invmx_triangular.

Variable R : comUnitRingType.

Lemma invmx_uniq m (M M' : 'M[R]_m) (H : M *m M' = 1%:M) : M' = invmx M.
Proof.
have [hM _] := (mulmx1_unit H).
by rewrite -[M']mulmx1 -(mulmxV hM) mulmxA (mulmx1C H) mul1mx.
Qed.

Fixpoint invmx_lower (m : nat) : 'M[R]_m -> 'M[R]_m :=
  match m return 'M[R]_m -> 'M[R]_m with
  | S p => fun (M : 'M[R]_(1 + p)) =>
           let: N := invmx_lower (drsubmx M) in
           block_mx 1%:M 0 (- N *m dlsubmx M) N
  | O => fun _ => 1%:M
  end.

Definition invmx_upper m (M : 'M[R]_m) := (invmx_lower M^T)^T.

(* lower triangular *)
Definition lower m (M : 'M[R]_m) :=
  forall (i j : 'I_m), i <= j -> M i j = (i == j)%:R.

Definition upper m (M : 'M[R]_m) := lower M^T.

Lemma drlower m (M : 'M[R]_(1 + m)) (H : lower M) : lower (drsubmx M).
Proof. by move=> i j hij; rewrite !mxE !rshift1 H. Qed.

Lemma urlower m (M : 'M[R]_(1 + m)) (H : lower M) : ursubmx M = 0.
Proof. by apply/rowP=> i; rewrite !mxE lshift0 rshift1 H. Qed.

Lemma ullower m (M : 'M[R]_(1 + m)) (H : lower M) : ulsubmx M = 1%:M.
Proof. by apply/rowP=> i; rewrite !mxE !ord1 H. Qed.

Lemma invmx_lowerE : forall m (M : 'M[R]_m), lower M -> M *m invmx_lower M = 1%:M.
Proof.
elim=> [M |n ih]; first by rewrite !thinmx0.
rewrite [n.+1]/(1 + n)%N => M hM /=.
rewrite -{1}[M]submxK (@mulmx_block _ 1 n 1 n 1 n).
rewrite ?(mulmx0,mulmx1,add0r) ih; last by apply/drlower.
rewrite (urlower hM) !mul0mx addr0 mulmxA mulmxN ih; last by apply/drlower.
by rewrite mulNmx mul1mx subrr ullower -?scalar_mx_block.
Qed.

Lemma invmx_lowerP m (M : 'M[R]_m) (H : lower M) : invmx_lower M = invmx M.
Proof. by apply/invmx_uniq; rewrite invmx_lowerE. Qed.

Lemma invmx_upperP m (M : 'M[R]_m) : upper M -> invmx_upper M = invmx M.
Proof. 
by rewrite /upper=> hL; rewrite /invmx_upper invmx_lowerP // trmx_inv trmxK.
Qed.

End invmx_triangular.

(* General invmx - Assuming that we have Strassen *)
Section invmx.

Local Coercion nat_of_pos : positive >-> nat.

Lemma addpp p : xO p = (p + p)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Variable R : comUnitRingType.

(* More general hypotheses: *)
(* Variable strassen : forall (m n p : positive), 'M[R]_(m,n) -> 'M[R]_(n,p) -> 'M[R]_(m,p). *)
(* Hypothesis strassenP : forall (m n p : positive) (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)),  *)
(*   strassen M N = M *m N. *)

(* This suffices for the proof *)
Variable strassen : forall (m : positive), 'M[R]_m -> 'M[R]_m -> 'M[R]_m.
Hypothesis strassenP : forall (m : positive) (M N : 'M[R]_m), strassen M N = M *m N.

Section strassen_invmx_step.

Variables (p : positive) (A : 'M[R]_(p + p)).

Local Notation A11 := (ulsubmx A).
Local Notation A12 := (ursubmx A).
Local Notation A21 := (dlsubmx A).
Local Notation A22 := (drsubmx A).

Hypothesis H : A21 *m invmx A11 *m A12 - A22 \in unitmx. 
Hypothesis HA11 : A11 \in unitmx.

Definition strassen_invmx_step f : 'M[R]_(p + p) :=
  let R1  := f A11 in
  let R2  := strassen A21 R1 in
  let R3  := strassen R1 A12 in
  let R4  := strassen A21 R3 in
  let R5  := R4 - A22 in
  let R6  := f R5 in
  let C12 := strassen R3 R6 in
  let C21 := strassen R6 R2 in
  let R7  := strassen R3 C21 in
  let C11 := R1 - R7 in
  let C22 := - R6 in
  block_mx C11 C12 C21 C22.

Lemma strassen_invmx_stepP f : f =1 invmx -> strassen_invmx_step f = invmx A.
Proof.
move=> Hf; rewrite -[A]submxK /strassen_invmx_step.
rewrite !Hf !strassenP.
apply/invmx_uniq.
rewrite !mulmx_block ?(mul1mx,mulmx1,mulmx0,addr0,add0r).
(* Simplify ulsubmx *)
rewrite mulmxBr mulmxV // !mulmxA mulmxV // mul1mx subrK.
(* Simplify ursubmx *)
rewrite mulmxN subrr.
(* Simplify dlsubmx *)
rewrite mulmxBr !mulmxA -addrA -3!mulNmx -!mulmxDl [- _ + _]addrC.
rewrite -opprB mulNmx mulmxV // mulNmx mul1mx subrr mul0mx.
(* Simplify drsubmx *)
rewrite mulmxN -mulmxBl mulmxV //.
admit.
Admitted.

End strassen_invmx_step.

Fixpoint strassen_invmx {p : positive} :=
  match p return 'M[R]_p -> 'M[R]_p with
  | xH => fun M => invmx M
  | xI p => fun M => invmx M (* TODO: FIX THIS! *)
  | xO p => fun M =>
    let M := castmx (addpp p, addpp p) M in
    castmx (esym (addpp p), esym (addpp p)) (strassen_invmx_step M strassen_invmx)
end.


Lemma strassen_invmxP : forall (p : positive) (M : 'M[R]_p), strassen_invmx M = invmx M.
Proof.
elim=> // p ih M.
rewrite /= strassen_invmx_stepP //=.
  admit.
admit.
admit.
Admitted.

End invmx.

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