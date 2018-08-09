(* Inductively defined matrices over computable rings *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import ssralg fintype perm matrix  bigop zmodp mxalgebra.
Require Import cssralg cseqpoly.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

Section Matrix.

(* multsE needs commutativity *)
Variable R : comRingType.
Variable CR : cringType R.

Let zero := zero CR.

(* matrix structure in block
   a    l
   c    M
with a one element, l a line, c a column and M a Matrix
*)
Inductive Matrix : Type :=
 | eM
 | cM of CR & seq CR & seq CR & Matrix.

(* Eqtype *)
Fixpoint eqMatrix (m1 m2 : Matrix) :=
  match m1, m2 with
  | eM, eM => true
  | cM x1 l1 c1 m1 , cM x2 l2 c2 m2 =>
     (x1 == x2) && (l1 == l2) && (c1 == c2) && eqMatrix m1 m2
  | _, _ => false
  end.

Lemma eqMatrixP : Equality.axiom eqMatrix.
Proof.
rewrite /eqMatrix => m1 m2.
apply: (iffP idP) => [| ->]; last by elim: m2 => // x l c _ ->; rewrite !eqxx.
elim: m1 m2 => [[] //|] x1 l1 c1 m1 ih [] // x2 l2 c2 m2.
(repeat case/andP) => /eqP h1 /eqP h2 /eqP h3 h.
f_equal => //.
by apply: ih.
Qed.

Canonical Matrix_eqMixin := EqMixin eqMatrixP.
Canonical Matrix_eqType := Eval hnf in EqType Matrix Matrix_eqMixin.

(* Translation functions *)
Definition rV2seq (n:nat) (l : 'rV_n) : seq CR :=
  map (fun i => trans (l 0 i)) (enum 'I_n).

(* Translation from ssr row vector into seq *)
Lemma size_rV2seq: forall n (l: 'rV_(n)), size (rV2seq l) = n.
Proof.
rewrite /rV2seq => n l.
by rewrite size_map size_enum_ord.
Qed.

Lemma rV2seq0 : forall (l: 'rV_0), rV2seq l = [::].
Proof.
move => l.
by apply/size0nil; rewrite size_rV2seq.
Qed.

Lemma inj_rV2seq : forall n, injective (@rV2seq n).
Proof.
rewrite /rV2seq => n a b /=.
set l1 := map _ _.
set l2 := map _ _ => h.
apply/rowP => i.
have : nth (trans (a 0 i)) l1 i = nth (trans (a 0 i)) l2 i by rewrite h.
rewrite /l1 /l2 !(@nth_map _ i) -?enumT ?size_enum_ord ?ltn_ord //=.
move/inj_trans.
by rewrite !(@nth_map _ i) -?enumT ?size_enum_ord ?ltn_ord //= nth_ord_enum.
Qed.

(* Translation from ssr col vector into seq *)
Definition cV2seq (m : nat) (c : 'cV_m) : seq CR :=
  map (fun i => trans (c i 0)) (enum 'I_m).

Lemma cV2seq_trans : forall m (c : 'cV_m),
  cV2seq c = map trans (map (fun i => c i 0) (enum 'I_m)).
Proof.
rewrite /cV2seq => m c.
rewrite -map_comp.
by apply/eq_map => i /=.
Qed.

Lemma size_cV2seq: forall n (l: 'cV_(n)), size (cV2seq l) = n.
Proof.
rewrite /cV2seq => n l.
by rewrite size_map size_enum_ord.
Qed.

Lemma cV2seq0 : forall (c: 'cV_0), cV2seq c = [::].
Proof.
move => c.
by apply/size0nil; rewrite size_cV2seq.
Qed.

Lemma inj_cV2seq : forall n, injective (@cV2seq n).
rewrite /cV2seq => n a b /=.
set l1 := map _ _.
set l2 := map _ _ => h.
apply/colP => i.
have : nth (trans (a i 0)) l1 i = nth (trans (a i 0)) l2 i by rewrite h.
rewrite /l1 /l2 !(@nth_map _ i) -?enumT ?size_enum_ord ?ltn_ord //=.
move/inj_trans.
by rewrite !(@nth_map _ i) -?enumT ?size_enum_ord ?ltn_ord //= nth_ord_enum.
Qed.

(* Translation from ssr matrices to Matrix *)
Fixpoint mat2Matrix (n:nat) : forall (m:nat), 'M[R]_(n,m) -> Matrix :=
 match n as x return forall (m:nat), 'M[R]_(x,m) -> Matrix with
  | O => fun _ _ => eM
  | S p => fun m =>
     match m as y return 'M[R]_(1 + p,y) -> Matrix with
       | O => fun _ => eM
       | S q => fun (mat: 'M[R]_(1 + p,1 + q)) =>
         cM (trans (mat 0 0)) (rV2seq (ursubmx mat)) (cV2seq (dlsubmx mat))
         (mat2Matrix (drsubmx mat))
       end
  end.

Lemma inj_mat2Matrix : forall n m, injective (@mat2Matrix n m).
Proof.
elim => [ | n hi] [ | m] /=.
- by move => M N _; rewrite [M]thinmx0 [N]thinmx0.
- by move => M N _; rewrite [M]flatmx0 [N]flatmx0.
- by move => M N _; rewrite [M]thinmx0 [N]thinmx0.
rewrite [n.+1]/(1 + n)%N [m.+1]/(1 + m)%N => M N.
case => /inj_trans h /inj_rV2seq hl /inj_cV2seq hc /hi hM.
by rewrite -[M]submxK -[N]submxK hl hc hM [ulsubmx M]mx11_scalar
 [ulsubmx N]mx11_scalar !mxE !lshift0 h.
Qed.

Definition mat_trans_struct n m := Trans (@inj_mat2Matrix n m).

(* Reflection lemma *)
Lemma mat2MatrixP : forall (n m : nat) (p q : 'M[R]_(n,m)),
  reflect (p = q) (mat2Matrix p == mat2Matrix q).
Proof.
move=> n m p q.
apply: (iffP idP) => [/eqP|-> //].
exact: inj_mat2Matrix.
Qed.

(* a tool function that mix zip with map *)
Definition zipWith (A B C:Type) (f: A -> B -> C)
  (l : seq A) (l' :seq B) : seq C :=
 map (fun xy: A*B => let (x,y) := xy in f x y) (zip l l').

Lemma zipWith0 : forall (A B C: Type) (f : A -> B -> C)
  (l : seq A), zipWith f l [::] = [::].
Proof. by move=> A B C f []. Qed.

(* seq of zeroes, of size n *)
Definition zeroes (n:nat) : seq CR := nseq n zero.

Lemma map1 : forall (l :seq R), map ( *%R^~ 1) l = l.
Proof.
elim => [ | hd tl hi] //=.
by rewrite mulr1 hi.
Qed.

Lemma rV2seq_zeroes : forall n, rV2seq (0 : 'rV_n) = zeroes n.
Proof.
rewrite /rV2seq => [[|n]].
- apply/size0nil.
  by rewrite size_map size_enum_ord.
apply/(@eq_from_nth _ zero).
- by rewrite size_map size_enum_ord size_nseq.
move => i.
rewrite size_map size_enum_ord => hi.
by rewrite (@nth_map (ordinal (S n)) 0 CR zero) ?size_enum_ord
      ?nth_nseq ?hi ?mxE ?zeroE.
Qed.

Lemma cV2seq_zeroes : forall n, cV2seq ( 0 : 'cV_n) = zeroes n.
Proof.
rewrite /cV2seq => [[|n]].
- apply/size0nil.
  by rewrite size_map size_enum_ord.
apply/(@eq_from_nth _ zero).
- by rewrite size_map size_enum_ord size_nseq.
move => i.
rewrite size_map size_enum_ord => hi.
by rewrite (@nth_map (ordinal (S n)) 0 CR zero) ?size_enum_ord
      ?nth_nseq ?hi ?mxE ?zeroE.
Qed.

(* 0 Matrix of size m x n *)
Fixpoint zerom (m n:nat) : Matrix :=
 match m,n with
  | S p, S q => cM zero (zeroes q) (zeroes p) (zerom p q)
  | _,_ => eM
end.

Lemma zeromE m n : mat2Matrix (0: 'M[R]_(m,n)) = (zerom m n).
Proof.
elim : m n => [ | m hi] [ | n] //=.
set UR := ursubmx _.
set DL := dlsubmx _.
set DR := drsubmx _.
have -> : UR = 0 by apply/rowP => i; rewrite !mxE.
have -> : DL = 0 by apply/colP => i; rewrite !mxE.
have -> : DR = 0 by apply/matrixP => i j; rewrite !mxE.
by rewrite rV2seq_zeroes cV2seq_zeroes hi !mxE zeroE.
Qed.

Lemma mat2Matrix0n: forall m (M :'M[R]_(0,m)), mat2Matrix M = eM.
Proof.
by move => m M.
Qed.

Lemma mat2Matrix0m: forall n (M: 'M[R]_(n,0)), mat2Matrix M = eM.
Proof.
by case.
Qed.

Lemma cV2seqS : forall n a (c: 'cV[R]_n),
  cV2seq (col_mx a%:M c) = trans a :: cV2seq c.
Proof.
rewrite /cV2seq => [[ | n]] a c.
- rewrite [c]flatmx0 /=.
  apply/(@eq_from_nth _ zero).
  + by rewrite size_map size_enum_ord /= size_map size_enum_ord.
  move => i.
  rewrite size_map size_enum_ord => hi.
  rewrite (@nth_map _ 0) ?size_enum_ord // !mxE.
  case: splitP => j.
  + rewrite [j]ord1 (@nth_ord_enum (1 + 0) 0 (Ordinal hi)) /= => -> /=.
    by rewrite !mxE mulr1n.
  by case: j.
apply/(@eq_from_nth _ zero).
- by rewrite size_map size_enum_ord /= size_map size_enum_ord.
move => i.
rewrite size_map size_enum_ord => hi.
rewrite (@nth_map _ 0) ?size_enum_ord // !mxE.
case: splitP => j.
- rewrite [j]ord1 (@nth_ord_enum (1 + n.+1) 0 (Ordinal hi)) /= => -> /=.
  by rewrite !mxE mulr1n.
rewrite (@nth_ord_enum _ _ (Ordinal hi)) /= => -> /=.
rewrite (@nth_map (ordinal n.+1) 0) ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

Lemma rV2seqS : forall n a (r: 'rV[R]_n),
  rV2seq (row_mx a%:M r) = trans a :: rV2seq r.
Proof.
rewrite /rV2seq => [[ | n]] a r.
- rewrite [r]thinmx0 /=.
  apply/(@eq_from_nth _ zero).
  + by rewrite size_map size_enum_ord /= size_map size_enum_ord.
  move => i.
  rewrite size_map size_enum_ord => hi.
  rewrite (@nth_map _ 0) ?size_enum_ord // !mxE.
  case: splitP => j.
  + rewrite [j]ord1 (@nth_ord_enum (1 + 0) 0 (Ordinal hi)) /= => -> /=.
    by rewrite !mxE mulr1n.
  by case: j.
apply/(@eq_from_nth _ zero).
- by rewrite size_map size_enum_ord /= size_map size_enum_ord.
move => i.
rewrite size_map size_enum_ord => hi.
rewrite (@nth_map _ 0) ?size_enum_ord // !mxE.
case: splitP => j.
- rewrite [j]ord1 (@nth_ord_enum (1 + n.+1) 0 (Ordinal hi)) /= => -> /=.
  by rewrite !mxE mulr1n.
rewrite (@nth_ord_enum _ _ (Ordinal hi)) /= => -> /=.
rewrite (@nth_map (ordinal n.+1) 0) ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

(* addition on seq
   if l1 and l2 are not of the same size, the result is of
   size l1 (truncating l2 or adding trailing 0s to l2 if necessary)
 *)
Fixpoint adds (l1 l2 : seq CR) : seq CR :=
 match l1,l2 with
  | [::], _ => [::]
  | _, [::] => l1
  | hd :: tl, hd' :: tl' => (add hd hd') :: (adds tl tl')
end.

Lemma addsrVE : forall (n:nat),
 {morph (@rV2seq n) : l1 l2 / l1 + l2 >-> (adds l1 l2) }.
Proof.
elim => [ | n hi].
- by move => l1 l2; rewrite [l1]thinmx0 [l2]thinmx0 !rV2seq_zeroes addr0 /=
    rV2seq_zeroes.
change n.+1 with (1 + n)%N => l1 l2.
by rewrite -[l1]hsubmxK -[l2]hsubmxK [lsubmx l1]mx11_scalar
    [lsubmx l2]mx11_scalar !rV2seqS /= add_row_mx -raddfD rV2seqS
    hi addE.
Qed.

Lemma addscVE: forall (n:nat),
 {morph (@cV2seq n) : c1 c2 / c1 + c2 >-> (adds c1 c2)}.
Proof.
elim => [ | n hi].
- by move => c1 c2; rewrite [c1]flatmx0 [c2]flatmx0 !cV2seq_zeroes addr0 /=
    cV2seq_zeroes.
change n.+1 with (1 + n)%N => c1 c2.
by rewrite -[c1]vsubmxK -[c2]vsubmxK [usubmx c1]mx11_scalar
    [usubmx c2]mx11_scalar !cV2seqS /= add_col_mx -raddfD cV2seqS
    hi addE.
Qed.

Lemma adds_nil: forall l, adds l [::] = l.
Proof. by case. Qed.

(* addition of Matrix *)
Fixpoint addM (m1 m2 : Matrix) : Matrix :=
 match m1,m2 with
  | eM, _ => m2
  | _, eM => m1
  | cM a1 l1 c1 m1, cM a2 l2 c2 m2 =>
    cM (add a1 a2) (adds l1 l2) (adds c1 c2) (addM m1 m2)
end.

Lemma addME : forall (n m : nat),
  {morph (@mat2Matrix n m) : A B / A + B >-> addM A B}.
Proof.
elim => [ | n hi] [ | m].
- by move => A B; rewrite [A]thinmx0 [B]thinmx0 addr0.
- by move => A B; rewrite [A]flatmx0 [B]flatmx0 addr0.
- by move => A B; rewrite [A]thinmx0 [B]thinmx0 addr0.
rewrite -[n.+1]/(1 + n)%N -[m.+1]/(1 + m)%N => A B; symmetry.
rewrite -{1}[A]submxK -{1}[B]submxK [ulsubmx A]mx11_scalar
  [ulsubmx B]mx11_scalar ![mat2Matrix (block_mx _ _ _ _)]/=.
  rewrite !block_mxKur !block_mxKdr !block_mxKdl !mxE !lshift0.
  case: splitP => x //; rewrite [x]ord1 {x} !mxE => _.
  case: splitP => x //; rewrite [x]ord1 {x} !mxE !mulr1n => _ /=.
  by rewrite -addsrVE -addscVE -hi !mxE -!raddfD /= addE.
Qed.

Lemma add_eM: forall M, addM M eM = M.
Proof. by case. Qed.

End Matrix.

Section MatrixMap.

Variable R R': comRingType.
Variable CR: cringType R.
Variable CR': cringType R'.

Fixpoint mapM (f: CR -> CR') (M: Matrix CR) {struct M} : Matrix CR' :=
  match M with
    | eM => @eM _ _
    | cM a l c M => cM (f a) (map f l) (map f c) (mapM f M)
  end.


Lemma rV2seq_map : forall (f: R -> R') (g: CR -> CR'),
  (forall a, trans (f a) = g (trans a))->
  forall (m:nat) (l: 'rV[R]_m),
  rV2seq _ (map_mx f l) = map g  (rV2seq _ l).
Proof.
move => f g h.
elim => [ | m hi].
- by move => l; rewrite [l]thinmx0 /= !rV2seq0.
rewrite [m.+1]/(1 + m)%N => l.
rewrite -[l]hsubmxK [lsubmx l]mx11_scalar !mxE !lshift0
  (@map_row_mx _ _ _ 1 1).
by rewrite [map_mx f (l 0%R 0%R)%:M]mx11_scalar !rV2seqS !mxE mulr1n /= h hi.
Qed.

Lemma cV2seq_map : forall (f: R -> R') (g: CR -> CR'),
 (forall a, trans (f a) = g (trans a))->
 forall (m:nat) (c: 'cV[R]_m),
  cV2seq _ (map_mx f c) = map g  (cV2seq _ c).
Proof.
move => f g h.
elim => [ | m hi].
- by move => c; rewrite [c]flatmx0 /= !cV2seq0.
rewrite [m.+1]/(1 + m)%N => c  .
rewrite -[c]vsubmxK [usubmx c]mx11_scalar !mxE !lshift0
  (@map_col_mx _ _ _ 1 _ 1).
by rewrite [map_mx f (c 0%R 0%R)%:M]mx11_scalar !cV2seqS !mxE mulr1n /= h hi.
Qed.


Lemma mat2Matrix_map : forall (f: R -> R') (g: CR -> CR'),
  (forall a: R, trans (f a) = g (trans a))->
  forall (m n:nat)  (M: 'M[R]_(m,n)),
  mat2Matrix _ (map_mx f M) = mapM g (mat2Matrix _ M).
Proof.
move => f g h.
elim => [ | m hi] [ | n].
- by move => M; rewrite [M]flatmx0 /=.
- by move => M; rewrite [M]flatmx0 /=.
- by move => M; rewrite [M]thinmx0 /=.
rewrite [m.+1]/(1 + m)%N [n.+1]/(1 + n)%N => M.
rewrite -[M]submxK (@map_block_mx _ _ _ 1 _ 1)
 [map_mx f (ulsubmx M)]mx11_scalar [mat2Matrix _ _]/=
  !mxE !lshift0 /= !block_mxKur !block_mxKdl !block_mxKdr.
case: splitP => x //; rewrite [x]ord1 !mxE {x} => _.
case: splitP => x //; rewrite [x]ord1 !mxE {x} => _.
case: splitP => x //; rewrite [x]ord1 !mxE {x} => _.
case: splitP => x //; rewrite [x]ord1 !mxE {x} => _.
by rewrite h (cV2seq_map h) (rV2seq_map h) hi !lshift0.
Qed.
End MatrixMap.

Section MatrixStruct.
Variable R : comRingType.
Variable CR : cringType R.

Definition oppM (M: Matrix CR) := mapM (@opp R CR)  M.
Definition subM (M N: Matrix CR) := addM M (oppM N).

Lemma oppME : forall (m n:nat),
  {morph (@mat2Matrix _ _ m n) : M / - M >-> (oppM M)}.
Proof.
rewrite /oppM => m n M.
rewrite -(@mat2Matrix_map _ _ _ _ (fun x => - x) (@opp R CR)) //.
  by f_equal; apply/matrixP => i j; rewrite !mxE.
by move => a; rewrite oppE.
Qed.

Lemma subME : forall (m n:nat),
  {morph (@mat2Matrix _ _ m n) : M N / M - N >-> (subM M N)}.
Proof.
rewrite /subM => m n M N.
by rewrite addME oppME.
Qed.

Definition Matrix_czMixin m n := @CZmodMixin
  [zmodType of 'M[R]_(m,n)] (Matrix CR) (zerom CR m n)
  oppM (@addM R CR) (mat_trans_struct CR m n) (zeromE CR m n)
  (@oppME m n) (@addME R CR m n).

Canonical Structure matrix_czType m n :=
  Eval hnf in CZmodType ('M[R]_(m,n)) (Matrix CR) (Matrix_czMixin m n).

End MatrixStruct.

Section MatrixFacts.
Variable R R': comRingType.
Variable CR : cringType R.
Variable CR' : cringType R'.

Lemma map_mxE: forall (f: R -> R') (g: CR -> CR'),
  (forall a: R, trans (f a) = g (trans a))->
  forall (m n:nat)  (M: 'M[R]_(m,n)),
  trans (map_mx f M) = mapM g (trans M).
Proof.
rewrite /trans => f g ha m n M /=.
by apply: mat2Matrix_map.
Qed.

Lemma block_mxE : forall (n p:nat) a (l: 'rV[R]_n) (c: 'cV[R]_p)
  (M: 'M[R]_(p,n)),
  trans (block_mx a%:M l c M) =
  cM (trans a) (rV2seq CR l) (cV2seq CR c) (trans M).
Proof.
move => n p a l c M.
rewrite /trans /= /trans /= block_mxKur block_mxKdr block_mxKdl !mxE.
case: splitP => x //; rewrite  [x]ord1 {x} !mxE => _.
by case: splitP => x //; rewrite  [x]ord1 {x} !mxE.
Qed.

Let zero := zero CR.
Let one  := one CR.

(* multiplication of a seq by a scalar *)
Definition multEV (a : CR) (l: seq CR) : seq CR := map (mul a) l.

Lemma multErVE : forall (n:nat) (a : R),
 {morph (@rV2seq R CR n) : l / a *: l >-> multEV (trans a) l}.
Proof.
elim => [ | n hi] a.
- by move => l; rewrite [l]thinmx0 scaler0 rV2seq_zeroes.
change (n.+1) with (1 + n)%N => l.
by rewrite -[l]hsubmxK [lsubmx l]mx11_scalar scale_row_mx
    [a *: ((lsubmx l) 0 0)%:M]mx11_scalar !rV2seqS /= hi !mxE mulr1n mulE.
Qed.

Lemma multEcVE : forall (n:nat) (a:R),
 {morph (@cV2seq R CR n) : c / a *: c >-> multEV (trans a) c}.
Proof.
elim => [ | n hi] a.
- by move => c; rewrite [c]flatmx0 scaler0 cV2seq_zeroes.
change (n.+1) with (1 + n)%N => c.
by rewrite -[c]vsubmxK [usubmx c]mx11_scalar scale_col_mx
    [a *: ((usubmx c) 0 0)%:M]mx11_scalar !cV2seqS /= hi !mxE mulr1n mulE.
Qed.

Fixpoint multEM (a: CR) (A : Matrix CR) : Matrix CR :=
 match A with
   | eM => (@eM _ _)
   | cM g l c M => cM (mul a g) (map (mul a) l) (map (mul a) c)
     (multEM a M)
end.

Lemma multEME : forall (m n:nat) (a: R) (A: 'M[R]_(m,n)),
  trans (a *: A) = multEM (trans a) (trans A).
Proof.
elim => [ | m hi] [ | n] a //.
rewrite [m.+1]/(1 + m)%N [n.+1]/(1 + n)%N => M.
rewrite -[M]submxK [ulsubmx M]mx11_scalar !mxE !lshift0
 (@scale_block_mx _ 1 m 1 n) scale_scalar_mx !block_mxE /= mulE; f_equal.
- by rewrite multErVE.
- by rewrite multEcVE.
by rewrite hi.
Qed.

Lemma map_mulC : forall (a : R) (l : seq R),
  map ((@mul _ CR) ^~ (trans a)) (map (trans) l) =
  map [eta mul (trans a)] (map (trans) l).
Proof.
move => a; elim => [ | hd tl hi] //=.
by rewrite -!mulE mulrC hi.
Qed.

(* multiplication of two seq which ends up in a Matrix (column * line) *)
Fixpoint mults (c l : seq CR) : Matrix CR :=
    match c,l with
     | [::], _ => (@eM _ _)
     | _, [::] => (@eM _ _)
     | u :: us, v :: vs =>
       cM (mul u v) (map (fun x => mul u x) vs)
          (map (fun x => mul x v) us)
          (mults us vs)
end.

Lemma multsE: forall (n m:nat) (c: 'cV[R]_n) (l: 'rV[R]_m),
  trans (c *m l) = mults (cV2seq CR c) (rV2seq CR l).
Proof.
elim => [ | n hi] [ | m].
- move => c l; rewrite [c]flatmx0 [l]thinmx0 mulmx0.
  by rewrite cV2seq_zeroes rV2seq_zeroes /=.
- move => c l; rewrite [c]flatmx0 mul0mx.
  by rewrite cV2seq_zeroes /=.
- move => c l; rewrite [l]thinmx0 mulmx0.
  rewrite rV2seq_zeroes /=.
  by case (cV2seq _ c).
rewrite [n.+1]/(1 + n)%nat [m.+1]/(1 + m)%nat => c l.
by rewrite -[c]vsubmxK -[l]hsubmxK [usubmx c]mx11_scalar
  [lsubmx l]mx11_scalar (@mul_col_row _ 1 _ 1 1)
  -scalar_mxM cV2seqS rV2seqS block_mxE /=
  hi mulE mul_scalar_mx multErVE mul_mx_scalar multEcVE
  cV2seq_trans map_mulC.
Qed.

(* identity Matrix of size n x n *)
Fixpoint ident (n:nat) : Matrix CR :=
 if n is (S p) then
  let z := zeroes _ p in
    cM one z z (ident p)
 else (@eM _ _).

Lemma idmxE : forall n, trans (1%:M : 'M[R]_n) = ident n.
Proof.
elim => [ | n hi] //=.
by rewrite [1%:M : 'M[R]_(1 + n)]scalar_mx_block block_mxE
        hi rV2seq_zeroes cV2seq_zeroes oneE.
Qed.

End MatrixFacts.

(* cMatrix over dvdring *)
Require Import dvdring cdvdring.

Section dvdMatrix.

Variable R : dvdRingType.
Variable CR : cdvdRingType R.

Lemma odfltE : forall (a: R) (b: option R),
  trans (odflt a b) = odflt (trans a) (omap (@trans _ CR) b).
Proof. by move => a [ b |]. Qed.

Definition divM (d t: CR) (M: Matrix CR) :=
  mapM (fun x => odflt t (cdiv x d)) M.

Lemma divME : forall (m n: nat) (d t: R) (M: 'M[R]_(m,n)),
  trans (map_mx (fun x => odflt t (x %/? d)) M) =
  divM (trans d) (trans t) (trans M).
Proof.
rewrite /divM => [[ | m ]] [ | n] d t.
- by move => M; rewrite [M]thinmx0 /=.
- by move => M; rewrite [M]flatmx0 /=.
- by move => M; rewrite [M]thinmx0 /=.
rewrite [m.+1]/(1 + m)%N [n.+1]/(1 + n)%N => M.
rewrite -[M]submxK /= !mxE /trans /=
 -map_ursubmx -map_dlsubmx -map_drsubmx
   block_mxKur block_mxKdl !block_mxKdr.
case: splitP => x // _; rewrite [x]ord1 !mxE; clear x.
case: splitP => x // _; rewrite [x]ord1 !mxE; clear x.
case: splitP => x // _; rewrite [x]ord1 !mxE !lshift0; clear x.
set f := fun x => odflt t (x %/? d).
set g := fun x => odflt (trans t) (cdiv x (trans d)).
have h : forall a, trans (f a) = g (trans a)
  by rewrite /f /g => a; rewrite odfltE cdivE.
by rewrite h (rV2seq_map h) (cV2seq_map h) (mat2Matrix_map h).
Qed.

End dvdMatrix.