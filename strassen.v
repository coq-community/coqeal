(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix mxtens seqmatrix cssralg.

(** This file describes a formally verified implementation of Strassen's
algorithm (Winograd's variant). *)

Section Strassen_exp2.

Local Open Scope nat_scope.

(* We define the exponential in terms of a sum, so that recursive calls on *)
(* blocks do not require casts. Suggested by Georges Gonthier.             *)
Definition exp2 := fun i => iter i (fun x => x + x) 1.

Local Open Scope ring_scope.

Variable (R : ringType).

(** We define a ring instance on ssreflect matrices so that the ring tactic
(based on type classes since Coq 8.4) may be used to solve identities
involving matrices. *)

Section matrixRing.

Variable n : nat.

Global Instance Zops : @Ring_ops (matrix_zmodType R n n) 0%R
  (scalar_mx 1) (@addmx R _ _) mulmx (fun M N => M - N) (@oppmx R _ _) eq.

Global Instance Zr: (@Ring _ _ _ _ _ _ _ _ Zops).
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

End matrixRing.

(** As a first prototype, we express Strassen's algorithm on matrices whose
sizes are powers of 2. The general algorithm is developed independently below. *)

Fixpoint Strassen_exp2 {k} :=
  match k return let M := 'M[R]_(exp2 k) in M -> M -> M with
  | 0%N => fun A B => A *m B
  | l.+1 => fun A B =>
    if l <= 5 then A *m B else
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
    let C21 := Strassen_exp2 X Y in
    let X := A21 + A22 in
    let Y := B12 - B11 in
    let C22 := Strassen_exp2 X Y in
    let X := X - A11 in
    let Y := B22 - Y in
    let C12 := Strassen_exp2 X Y in
    let X := A12 - X in
    let C11 := Strassen_exp2 X B22 in
    let X := Strassen_exp2 A11 B11 in
    let C12 := X + C12 in
    let C21 := C12 + C21 in
    let C12 := C12 + C22 in
    let C22 := C21 + C22 in
    let C12 := C12 + C11 in
    let Y := Y - B21 in
    let C11 := Strassen_exp2 A22 Y in
    let C21 := C21 - C11 in
    let C11 := Strassen_exp2 A12 B21 in
    let C11 := X + C11 in
    block_mx C11 C12 C21 C22
  end.

Import GRing.Theory.

Lemma Strassen_exp2P : forall n (M N : 'M[R]_(exp2 n)), (Strassen_exp2 M N) = (M *m N).
Proof.
elim=>[M N|n IHn M N] //=.
case:ifP=> _ // ; symmetry.
rewrite !IHn -{1}(submxK M) -{1}(submxK N) mulmx_block .
congr block_mx.
by non_commutative_ring.
by non_commutative_ring.
by non_commutative_ring.
Qed.

Variable CR : cringType R.

Fixpoint Strassen_exp2_seqmx k :=
  match k return let M := seqmatrix CR in M -> M -> M with
  | 0%N => fun A B => mulseqmx (exp2 k) (exp2 k) A B
  | l.+1 => fun A B =>
    if l <= 5 then mulseqmx (exp2 k) (exp2 k) A B else
    let off := exp2 l in
    let A11 := ulsubseqmx off off A in
    let A12 := ursubseqmx off off A in
    let A21 := dlsubseqmx off off A in
    let A22 := drsubseqmx off off A in
    let B11 := ulsubseqmx off off B in
    let B12 := ursubseqmx off off B in
    let B21 := dlsubseqmx off off B in
    let B22 := drsubseqmx off off B in
    let X := subseqmx A11 A21 in
    let Y := subseqmx B22 B12 in
    let C21 := Strassen_exp2_seqmx l X Y in
    let X := addseqmx A21 A22 in
    let Y := subseqmx B12 B11 in
    let C22 := Strassen_exp2_seqmx l X Y in
    let X := subseqmx X A11 in
    let Y := subseqmx B22 Y in
    let C12 := Strassen_exp2_seqmx l X Y in
    let X := subseqmx A12 X in
    let C11 := Strassen_exp2_seqmx l X B22 in
    let X := Strassen_exp2_seqmx l A11 B11 in
    let C12 := addseqmx X C12 in
    let C21 := addseqmx C12 C21 in
    let C12 := addseqmx C12 C22 in
    let C22 := addseqmx C21 C22 in
    let C12 := addseqmx C12 C11 in
    let Y := subseqmx Y B21 in
    let C11 := Strassen_exp2_seqmx l A22 Y in
    let C21 := subseqmx C21 C11 in
    let C11 := Strassen_exp2_seqmx l A12 B21 in
    let C11 := addseqmx X C11 in
    block_seqmx C11 C12 C21 C22
  end.

Variable k : nat.

Lemma Strassen_exp2_seqmxP :
  {morph (@seqmx_of_mx _ CR (exp2 k) (exp2 k)) :
    M N / Strassen_exp2 M N >-> Strassen_exp2_seqmx k M N}.
Proof.
elim:k=> [|k' IHn] /= M N ; first by rewrite /= mulseqmxE.
rewrite {1}/Strassen_exp2_seqmx {1}/Strassen_exp2.
case:ifP=> _; first by rewrite mulseqmxE.
rewrite -/Strassen_exp2_seqmx -/Strassen_exp2.
rewrite !drsubseqmxE !dlsubseqmxE !ulsubseqmxE !ursubseqmxE.
rewrite -!{1}subseqmxE -!{1}addseqmxE -!{1}subseqmxE.
rewrite -!IHn.
rewrite -!{1}addseqmxE -!{1}subseqmxE.
by rewrite -block_seqmxE.
Qed.

End Strassen_exp2.

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

Variable CR : cringType R.

Definition Strassen_step_seqmx (p : positive) (A B : seqmatrix CR) f : seqmatrix CR :=
  let A11 := ulsubseqmx p p A in
  let A12 := ursubseqmx p p A in
  let A21 := dlsubseqmx p p A in
  let A22 := drsubseqmx p p A in
  let B11 := ulsubseqmx p p B in
  let B12 := ursubseqmx p p B in
  let B21 := dlsubseqmx p p B in
  let B22 := drsubseqmx p p B in
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

Lemma Strassen_step_seqmxP (p : positive) f fI :
  {morph (@seqmx_of_mx _ CR p p) : M N / f M N >-> fI p M N} ->
  {morph (@seqmx_of_mx _ CR (p + p) (p + p)) :
    M N / Strassen_step M N f >-> Strassen_step_seqmx p M N fI}.
Proof.
move=> Hf M N; rewrite /Strassen_step_seqmx !ulsubseqmxE !ursubseqmxE !dlsubseqmxE.
rewrite !drsubseqmxE -!subseqmxE -!addseqmxE -!subseqmxE -!Hf -!addseqmxE.
by rewrite -!subseqmxE block_seqmxE.
Qed.

Fixpoint Strassen_seqmx (n : positive) :=
  match n return let M := seqmatrix CR in M -> M -> M with
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

Lemma Strassen_seqmxP : forall (p : positive),
  {morph (@seqmx_of_mx _ CR p p) : M N / Strassen M N >-> Strassen_seqmx p M N}.
Proof.
elim=> [p IHp /= M N|p IHp /= M N|M N /=].
* case:ifP=> _; first by rewrite mulseqmxE.
  rewrite cast_seqmx -block_seqmxE; congr block_seqmx.
  + rewrite addseqmxE (Strassen_step_seqmxP _ _ (Strassen_seqmx)) // -mulseqmxE.
    rewrite -!ulsubseqmxE -!ursubseqmxE -!dlsubseqmxE !cast_seqmx.
    by rewrite addnn -NatTrec.doubleE.
  + rewrite addseqmxE -!mulseqmxE.
    rewrite -ulsubseqmxE -!ursubseqmxE -drsubseqmxE !cast_seqmx addnn.
    by rewrite -NatTrec.doubleE.
  + rewrite addseqmxE -!mulseqmxE.
    rewrite -ulsubseqmxE -!dlsubseqmxE -drsubseqmxE !cast_seqmx.
    by rewrite addnn -NatTrec.doubleE.
  + rewrite addseqmxE -!mulseqmxE.
    rewrite -dlsubseqmxE -!drsubseqmxE -ursubseqmxE !cast_seqmx.
    by rewrite addnn -NatTrec.doubleE.
* case:ifP=> _.
    by rewrite mulseqmxE // NatTrec.doubleE -addnn.
  by rewrite cast_seqmx (Strassen_step_seqmxP _ _ (Strassen_seqmx)) // !cast_seqmx.
by rewrite mulseqmxE.
Qed.

End Strassen.