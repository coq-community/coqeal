(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements seqmatrix.

(** This file describes a formally verified implementation of Strassen's
algorithm (Winograd's variant). *)

Instance Zops (R : ringType) (n : nat) : @Ring_ops 'M[R]_n 0%R
  (scalar_mx 1) (@addmx R _ _) mulmx (fun M N => M - N)%R (@oppmx R _ _) eq.

Instance Zr (R : ringType) (n : nat) : (@Ring _ _ _ _ _ _ _ _ (Zops R n)).
Proof.
constructor=> //.
  + exact:eq_equivalence.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1; rewrite H1.
  + exact:add0mx.
  + exact:addmxC.
  + exact:addmxA.
  + exact:mul1mx.
  + exact:mulmx1.
  + exact:mulmxA.
  + exact:mulmxDl.
  + by move=> M N P ; exact:mulmxDr.
  + by move=> M; rewrite /addition /add_notation (addmxC M) addNmx.
Qed.

(** We now define Strassen's algorithm on matrices of general shape.
Input matrices are treated using dynamic peeling. *)

Section Strassen.

Local Open Scope ring_scope.

(** K is the size threshold below which we switch back to naive
multiplication *)
Variable R : ringType.
Let K := 32%positive.

Local Coercion nat_of_pos : positive >-> nat.

Lemma addpp p : xO p = (p + p)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addSpp p : xI p = (p + p).+1%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addp1 p : xI p = (xO p + 1)%N :> nat.
Proof. by rewrite addn1. Qed.

Lemma addpp1 p : xI p = (p + p + 1)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn addn1. Qed.

Lemma lt0p : forall p : positive, 0 < p.
Proof.
by elim=> // p IHp /=; rewrite NatTrec.doubleE -addnn; exact:ltn_addl.
Qed.

Definition Strassen_step {p : positive} (A B : 'M[R]_(p + p)) f : 'M[R]_(p + p) :=
  let A11 := ulsubmx A in
  let A12 := ursubmx A in
  let A21 := dlsubmx A in
  let A22 := drsubmx A in
  let B11 := ulsubmx B in
  let B12 := ursubmx B in
  let B21 := dlsubmx B in
  let B22 := drsubmx B in
  let X := A11 - A21 in
  let Y := B22 - B12 in
  let C21 := f X Y in
  let X := A21 + A22 in
  let Y := B12 - B11 in
  let C22 := f X Y in
  let X := X - A11 in
  let Y := B22 - Y in
  let C12 := f X Y in
  let X := A12 - X in
  let C11 := f X B22 in
  let X := f A11 B11 in
  let C12 := X + C12 in
  let C21 := C12 + C21 in
  let C12 := C12 + C22 in
  let C22 := C21 + C22 in
  let C12 := C12 + C11 in
  let Y := Y - B21 in
  let C11 := f A22 Y in
  let C21 := C21 - C11 in
  let C11 := f A12 B21 in
  let C11 := X + C11 in
  block_mx C11 C12 C21 C22.

Lemma Strassen_stepP (p : positive) (A B : 'M[R]_(p + p)) f :
  f =2 mulmx -> Strassen_step A B f = A *m B.
Proof.
move=> Hf; rewrite -{2}[A]submxK -{2}[B]submxK mulmx_block /Strassen_step !Hf.
rewrite /GRing.add /= /GRing.opp /=.
by congr block_mx; non_commutative_ring.
Qed.

Fixpoint Strassen {n : positive} {struct n} :=
  match n return let M := 'M[R]_n in M -> M -> M with
  | xH => fun M N => M *m N
  | xO p => fun A B =>
    if p <= K then A *m B else
    let A := castmx (addpp p,addpp p) A in
    let B := castmx (addpp p,addpp p) B in
    castmx (esym (addpp p),esym (addpp p)) (Strassen_step A B Strassen)
  | xI p => fun M N =>
    if p <= K then M *m N else
    let M := castmx (addpp1 p, addpp1 p) M in
    let N := castmx (addpp1 p, addpp1 p) N in
    let M11 := ulsubmx M in
    let M12 := ursubmx M in
    let M21 := dlsubmx M in
    let M22 := drsubmx M in
    let N11 := ulsubmx N in
    let N12 := ursubmx N in
    let N21 := dlsubmx N in
    let N22 := drsubmx N in
    let C := Strassen_step M11 N11 Strassen + M12 *m N21 in
    let R12 := M11 *m N12 + M12 *m N22 in
    let R21 := M21 *m N11 + M22 *m N21 in
    let R22 := M21 *m N12 + M22 *m N22 in
    castmx (esym (addpp1 p), esym (addpp1 p)) (block_mx C R12 R21 R22)
end.

Lemma mulmx_cast {R' : ringType} {m n p m' n' p'} {M:'M[R']_(m,p)} {N:'M_(p,n)}
  {eqm : m = m'} (eqp : p = p') {eqn : n = n'} :
  castmx (eqm,eqn) (M *m N) = castmx (eqm,eqp) M *m castmx (eqp,eqn) N.
Proof. by case eqm ; case eqn ; case eqp. Qed.

Lemma StrassenP : forall (n : positive) (M N : 'M[R]_n), Strassen M N = M *m N.
Proof.
elim=> // [p IHp|p IHp] M N.
  rewrite /=; case:ifP=> // _.
  by rewrite Strassen_stepP // -mulmx_block !submxK -mulmx_cast castmxK.
rewrite /=; case:ifP=> // _.
by rewrite Strassen_stepP // -mulmx_cast castmxK.
Qed.

Section Strassen_seqmx.

Variable A : Type.

Import Refinements.Op.

Context `{zero A, opp A, add A, sub A, mul A, eq A}.

Definition Strassen_step_seqmx (p : positive) (a b : seqmatrix A) f : seqmatrix A :=
  let A11 := ulsubseqmx p p a in
  let A12 := ursubseqmx p p a in
  let A21 := dlsubseqmx p p a in
  let A22 := drsubseqmx p p a in
  let B11 := ulsubseqmx p p b in
  let B12 := ursubseqmx p p b in
  let B21 := dlsubseqmx p p b in
  let B22 := drsubseqmx p p b in
  let X := subseqmx A11 A21 in
  let Y := subseqmx B22 B12 in
  let C21 := f p X Y in
  let X := addseqmx A21 A22 in
  let Y := subseqmx B12 B11 in
  let C22 := f p X Y in
  let X := subseqmx X A11 in
  let Y := subseqmx B22 Y in
  let C12 := f p X Y in
  let X := subseqmx A12 X in
  let C11 := f p X B22 in
  let X := f p A11 B11 in
  let C12 := addseqmx X C12 in
  let C21 := addseqmx C12 C21 in
  let C12 := addseqmx C12 C22 in
  let C22 := addseqmx C21 C22 in
  let C12 := addseqmx C12 C11 in
  let Y := subseqmx Y B21 in
  let C11 := f p A22 Y in
  let C21 := subseqmx C21 C11 in
  let C11 := f p A12 B21 in
  let C11 := addseqmx X C11 in
  block_seqmx C11 C12 C21 C22.

(*
Lemma Strassen_step_seqmxP (p : positive) f fI :
  {morph (@seqmx_of_mx _ CR p p) : M N / f M N >-> fI p M N} ->
  {morph (@seqmx_of_mx _ CR (p + p) (p + p)) :
    M N / Strassen_step M N f >-> Strassen_step_seqmx p M N fI}.
Proof.
move=> Hf M N; rewrite /Strassen_step_seqmx !ulsubseqmxE !ursubseqmxE !dlsubseqmxE.
rewrite !drsubseqmxE -!subseqmxE -!addseqmxE -!subseqmxE -!Hf -!addseqmxE.
by rewrite -!subseqmxE block_seqmxE.
Qed.
*)

Fixpoint Strassen_seqmx (n : positive) :=
  match n return let M := seqmatrix A in M -> M -> M with
  | xH => fun A B => mulseqmx n n A B
  | xO p => fun A B =>
    if p <= K then mulseqmx n n A B else
    Strassen_step_seqmx p A B Strassen_seqmx
  | xI p => fun M N =>
    if p <= K then mulseqmx n n M N else
    let off := xO p in
    let M11 := ulsubseqmx off off M in
    let M12 := ursubseqmx off off M in
    let M21 := dlsubseqmx off off M in
    let M22 := drsubseqmx off off M in
    let N11 := ulsubseqmx off off N in
    let N12 := ursubseqmx off off N in
    let N21 := dlsubseqmx off off N in
    let N22 := drsubseqmx off off N in
    let R12 := addseqmx (mulseqmx off 1 M11 N12) (mulseqmx 1 1 M12 N22) in
    let R21 := addseqmx (mulseqmx off off M21 N11) (mulseqmx 1 off M22 N21) in
    let R22 := addseqmx (mulseqmx off 1 M21 N12) (mulseqmx 1 1 M22 N22) in
    let C := addseqmx (Strassen_step_seqmx p M11 N11 Strassen_seqmx) (mulseqmx 1 off M12 N21) in
    block_seqmx C R12 R21 R22
  end.


End Strassen_seqmx.

Import Refinements.Op.

Local Instance zero_R : zero R := 0%R.
Local Instance opp_R : opp R := -%R.
Local Instance add_R : add R := +%R.
Local Instance sub_R : sub R := (fun x y => x - y)%R.
Local Instance mul_R : mul R := *%R.

Instance refines_Strassen_step_seqmx (p : positive) f fI :
  (forall (x y : 'M_p) a b, refines x a -> refines y b -> refines (f x y) (fI p a b)) ->
  forall (x y : 'M_(p+p)) a b, refines x a -> refines y b ->
  refines (Strassen_step x y f) (Strassen_step_seqmx _ p a b fI).
Proof.
move=> H x y a b ref_xa ref_yb.
rewrite /Strassen_step /Strassen_step_seqmx.
exact/refinesP.
Qed.

Instance refines_Strassen_seqmx (p : positive) (x y : 'M[R]_p) a b :
  refines x a -> refines y b -> refines (Strassen x y) (Strassen_seqmx R p a b).
Proof.
elim: p x y a b => [p IHp|p IHp|] x y a b ref_xa ref_yb.
* rewrite /Strassen /Strassen_seqmx.
case: ifP=> _; first exact/refinesP.
rewrite [nat_of_pos (p~0)]/= NatTrec.doubleE -addnn.
apply refines_cast_seqmx.
apply refines_block_seqmx.
rewrite -/Strassen -/(Strassen_seqmx _).
apply refines_addseqmx.
apply refines_Strassen_step_seqmx.
exact: IHp.
by apply/refinesP.
by apply/refinesP.
by apply/refinesP.
by apply/refinesP.
by apply/refinesP.
by apply/refinesP.
* rewrite /Strassen /Strassen_seqmx.
case: ifP=> _; first exact/refinesP.
rewrite -/Strassen -/(Strassen_seqmx _).
apply refines_cast_seqmx.
apply refines_Strassen_step_seqmx.
exact: IHp.
exact/refinesP.
exact/refinesP.
*rewrite /Strassen /Strassen_seqmx.
exact/refinesP.
Qed.

End Strassen.