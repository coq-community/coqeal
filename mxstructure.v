Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import ssralg fintype perm poly mxpoly.
Require Import matrix bigop zmodp mxtens.
Require Import ssrcomplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(***************** Triangular Matrices **************************)

Section Triangular.

Local Open Scope ring_scope.

Variable R : ringType.
Variables m n : nat.

Definition upper_part_mx (M : 'M[R]_(m,n)) := 
  \matrix_(i, j) (M i j *+ (i <= j)).

Definition lower_part_mx (M : 'M[R]_(m,n)) := 
  \matrix_(i, j) (M i j *+ (j <= i)).

Definition upper_triangular_mx M := M == upper_part_mx M.

Lemma upper_triangular_mxP {M : 'M_(m,n)} :
  reflect (forall (i : 'I_m) (j : 'I_n), j < i -> M i j = 0) 
          (upper_triangular_mx M).
Proof.
apply/(iffP idP)=> [H i j Hij|H].
  rewrite /upper_triangular_mx in H.
  by move/eqP:H=> ->; rewrite mxE leqNgt Hij.
apply/eqP/matrixP=> i j; rewrite mxE leqNgt; move:(H i j).
by case:(j < i)=> // ->.
Qed.

Definition lower_triangular_mx M := M == lower_part_mx M.

Definition is_triangular_mx M := upper_triangular_mx M || lower_triangular_mx M.

Lemma upper_triangular_mx0 : upper_triangular_mx 0.
Proof. by apply/upper_triangular_mxP=> i j; rewrite mxE. Qed.



End Triangular.

Section TriangularBlock.

Local Open Scope ring_scope.

Variable R : ringType.
Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables  (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Lemma upper_triangular_block_mxdl :
  upper_triangular_mx (block_mx Aul Aur Adl Adr) -> n1 <= m1 -> Adl = 0.
Proof.
move=> HA Hn1.
apply/matrixP=> i j.
transitivity (block_mx Aul Aur Adl Adr (rshift m1 i) (lshift n2 j)).
  by rewrite block_mxEdl.
rewrite (upper_triangular_mxP HA) ?mxE //=.
by apply:ltn_addr; exact:(leq_trans (ltn_ord j)).
Qed.

Lemma upper_triangular_block_mxdr :
  upper_triangular_mx (block_mx Aul Aur Adl Adr) -> n1 <= m1 ->
  upper_triangular_mx Adr.
Proof.
move/upper_triangular_mxP=> HA Hn1; apply/upper_triangular_mxP=> i j Hij.
rewrite -(HA (rshift m1 i) (rshift n1 j)) ?block_mxEdr // -addnS.
exact:leq_add.
Qed.

Lemma upper_triangular_block : upper_triangular_mx Aul -> m1 <= n1 ->
  upper_triangular_mx Adr -> upper_triangular_mx (block_mx Aul 0 0 Adr).
Proof.
move/upper_triangular_mxP=> HAul H /upper_triangular_mxP HAdr.
apply/upper_triangular_mxP=> i j Hij; rewrite !mxE.
case: splitP=> k Hk; rewrite !mxE; case: splitP=> l Hl.
 -by apply: HAul; rewrite -Hk -Hl.
 -by rewrite mxE.
 -by rewrite mxE.
apply: HAdr; rewrite -(ltn_add2l m1) -Hk.
rewrite Hl in Hij; apply: (leq_ltn_trans _ Hij).
by rewrite leq_add2r.
Qed.


End TriangularBlock.


Section SquareTriangular.

Local Open Scope ring_scope.
Variable R : comRingType.

Lemma det_triangular_mx : forall n (M : 'M[R]_n),
  upper_triangular_mx M -> \det M = \prod_i M i i.
Proof.
elim=> [M _|n IHn]; first by rewrite det_mx00 big_ord0.
rewrite -[n.+1]add1n=> M.
rewrite -(submxK M)=> HM.
rewrite (upper_triangular_block_mxdl HM) // det_ublock IHn.
  rewrite {1}[ulsubmx M]mx11_scalar det_scalar1 big_split_ord big_ord1.
  by rewrite block_mxEul; congr *%R; apply:eq_bigr=> i _; rewrite block_mxEdr.
exact:(upper_triangular_block_mxdr HM).
Qed.

Lemma char_poly_mx_triangular_mx n (M : 'M[R]_n) :
  upper_triangular_mx M -> upper_triangular_mx (char_poly_mx M).
Proof.
move/upper_triangular_mxP=> HM; apply/upper_triangular_mxP=>i j Hij.
rewrite !mxE .
have ->:(i == j) = false.
  apply/eqP=> Habs.
  rewrite Habs in Hij.
  suff: false => //.
  by rewrite -(ltnn j).
by rewrite (HM i j Hij) GRing.subr0.
Qed.

Lemma row'_col'_triangular_mx n (M : 'M[R]_n) i:
  upper_triangular_mx M -> upper_triangular_mx (row' i (col' i M)).
Proof.
move/upper_triangular_mxP=> HM; apply/upper_triangular_mxP=> j k Hij.
rewrite !mxE HM // /lift /= /bump /ltn -addn1 -addnA addn1.
apply: leq_add=> //; case H: (i <= k)=> //.
by rewrite (ltnW (leq_ltn_trans H Hij)).
Qed.


End SquareTriangular.

(************************************************************)
(******************* Block Diagonal Matrices ****************)

Section diag_block_ringType.

Variable R : ringType.
Local Open Scope ring_scope.
Import GRing.Theory.


Fixpoint szmxr k (s : seq nat) : nat :=
  match s with
   | nil => k
   | x :: s' => (k + (szmxr x s').+1)%N
 end.

  
Fixpoint dgbmxr k (s : seq nat) (F : (forall n, nat -> 'M[R]_n.+1)) :=
  match s return 'M_((szmxr k s).+1) with
    | nil => F k 0%N
    | x :: l => block_mx (F k 0%N) 0 0 (dgbmxr x l (fun n i => F n i.+1))
  end.


Fixpoint size_sum s :=
  match s with
   |nil => 0%N
   |x :: s' => szmxr x s'
 end.
 
Fixpoint diag_block_mx s F :=
  match s return 'M_((size_sum s).+1) with
    |nil => 0
    | x :: s' => dgbmxr x s' F
  end.


Lemma size_sum_big : forall s x,
  (size_sum (x :: s)).+1 = (\sum_(k <- x :: s) k.+1)%N.
Proof.
elim=> [s|n s IHn x] /=; rewrite big_cons.
   by rewrite big_nil addn0.
by rewrite IHn.
Qed.

Lemma ext_F s (F1 F2 : forall n, nat -> 'M_n.+1) : 
(forall i, i < size s -> 
  (F1 (nth 0%N s i) i) = (F2 (nth 0%N s i) i)) ->
  diag_block_mx s F1 = diag_block_mx s F2.
Proof.
case: s=> // a l.
elim: l a F1 F2=> /= [a F1 F2 Hi|b l IHl a F1 F2 Hi].
  exact: (Hi 0%N). 
set F3 := fun n i => _.
set F4 := fun n i => _.
rewrite (Hi 0%N) // (IHl b F3 F4) //.
by move=> i Hi2; apply: (Hi i.+1).
Qed.


Lemma upper_triangular_diag_block (s : seq nat) 
  (F : (forall n, nat -> 'M[R]_n.+1)) :
  (forall j, upper_triangular_mx (F (nth 0%N s j) j)) ->
  upper_triangular_mx (diag_block_mx s F).
Proof.
case: s=>[_|a l]; first exact: upper_triangular_mx0.
elim: l a F=> /= [a F H|b l IHl a F H]; first exact: (H 0%N).
apply: (@upper_triangular_block _ a.+1 _ a.+1)=> //.
  exact: (H 0%N).
by apply: IHl=> j; exact: (H j.+1).
Qed.


Lemma scalar_diag_block_mx c x s (F : forall n, nat -> 'M_n.+1) :
 (forall i, i < size (x :: s) -> F (nth 0%N (x :: s) i) i = c%:M ) ->
 diag_block_mx (x :: s) F = c%:M. 
Proof.
elim: s x F=> /= [a F Hi| b l IHl a F Hi].
  exact: (Hi 0%N).
rewrite (Hi 0%N) // IHl -?scalar_mx_block // => i Hi2.
exact: (Hi i.+1).
Qed.


Lemma diag_block_mx0 s (F : forall n, nat -> 'M_n.+1) :
 (forall i, i < size s -> F (nth 0%N s i) i = 0) ->
 diag_block_mx s F = 0. 
Proof.
case: s=> // a l Hi.
rewrite -(scale0r 1%:M) scalemx1.
apply: scalar_diag_block_mx=> i H.
by rewrite Hi // -(scale0r 1%:M) scalemx1.
Qed.

Lemma add_diag_block s F1 F2 :
 diag_block_mx s F1 + diag_block_mx s F2 = 
 diag_block_mx s (fun n i => F1 n i + F2 n i).
Proof.
case: s=> [|a l]; first by rewrite addr0.
elim: l a F1 F2=> //= b l IHl a F1 F2.
by rewrite -IHl (add_block_mx (F1 a 0%N)) !addr0.
Qed.

Lemma mulmx_diag_block s F1 F2 :
  diag_block_mx s F1 *m diag_block_mx s F2 =
  diag_block_mx s (fun n i => F1 n i *m F2 n i).
Proof. 
case: s=>[|a l]; first by rewrite mulmx0.
elim: l a F1 F2=> //= b l IHl a F1 F2.
rewrite -IHl (mulmx_block (F1 a 0%N) 0 0 _ (F2 a 0%N)).
by rewrite !mul0mx !mulmx0 addr0 !add0r.
Qed.

Lemma exp_diag_block_S s F k : 
 (diag_block_mx s F)^+ k.+1 = diag_block_mx s (fun n i => (F n i)^+ k.+1).
Proof.
case: s=>[|a l]; first by rewrite expr0n /=.
elim: l a F=> //= b l IHl a F.
by rewrite -IHl exp_block_mx.
Qed.

Lemma exp_diag_block_cons x s F k :
 (diag_block_mx (x :: s) F)^+ k = diag_block_mx (x :: s) (fun n i => (F n i)^+ k).
Proof.
elim: s x F => //= a l IHl x F.
by rewrite -IHl exp_block_mx.
Qed.

End diag_block_ringType.

 
Section diag_block_comRingType.

Variable R : comRingType.
Local Open Scope ring_scope.
Import GRing.Theory.


Lemma det_diag_block n s (F : forall n, nat -> 'M[R]_n.+1) : 
  \det (diag_block_mx (n :: s) F) = 
  \prod_(i < size (n :: s)) \det (F (nth 0%N (n :: s) i) i).
Proof.  
elim: s n F=>[n F|a l IHl n F] /=.
  by rewrite big_ord_recl big_ord0 mulr1 /=.
by rewrite (det_ublock (F n 0%N)) big_ord_recl IHl.
Qed.


Lemma horner_mx_diag_block (p : {poly R}) x s F : 
  horner_mx (diag_block_mx (x :: s) F) p = 
  diag_block_mx (x :: s) (fun n i => horner_mx (F n i) p).
Proof.
elim/poly_ind: p.
  rewrite rmorph0 diag_block_mx0 // => i _.
  by rewrite rmorph0.
move=> p c IHp.
set s1 := _ :: _.
set F1 := fun n i => _ _ (_ + _).
pose F2 := fun n i => horner_mx (F n i) p *m (F n i) + horner_mx (F n i) c%:P.
have Hi: forall i, i < size s1 -> F1 (nth 0%N s1 i) i = F2 (nth 0%N s1 i) i. 
  by move=> i _; rewrite /F1 /F2 rmorphD rmorphM /= horner_mx_X.
rewrite (ext_F Hi) /F2 -add_diag_block -mulmx_diag_block.
rewrite rmorphD rmorphM /=.
rewrite horner_mx_X horner_mx_C IHp.
set F3 := fun n i => _ _ c%:P.
rewrite -(@scalar_diag_block_mx _ c _ _ F3) // => i Hi2.
by rewrite /F3 horner_mx_C.
Qed.


End diag_block_comRingType.


Section diag_mx_seq.

Variable R : ringType.
Local Open Scope ring_scope.
Import GRing.Theory.

Definition diag_mx_seq m n (s : seq R) :=
   \matrix_(i < m, j < n) (nth 0%R s i *+ (i == j :> nat)).

(* Lemma cast_diag s : sizemx [seq existTmx (diag_mx_seq (size x) (size x) x) | x <- s] =  *)
(*   size (flatten s). *)
(* Proof. *)
(* by elim: s=> // a l; rewrite size_cat=> <-.  *)
(* Qed. *)

Lemma diag_mx_seq_nil m n : diag_mx_seq m n [::] = 0.
Proof.
by apply/matrixP=> i j; rewrite !mxE nth_nil mul0rn.
Qed.

Lemma diag_mx_seq_cons m n x (s :  seq R) :
  diag_mx_seq (1 + m) (1 + n) (x :: s) =
  block_mx x%:M 0 0 (diag_mx_seq m n s).
Proof.
apply/matrixP => i j; rewrite !mxE.
by case: splitP => i' ->; rewrite !mxE; case:splitP => j' ->; rewrite !mxE ?ord1.
Qed.

Lemma diag_mx_seq_cat m1 m2 n1 n2 (s1 s2 : seq R) :
  size s1 = m1 -> size s1 = n1 ->
  diag_mx_seq (m1 + m2) (n1 + n2) (s1 ++ s2) =
  block_mx (diag_mx_seq m1 n1 s1) 0 0 (diag_mx_seq m2 n2 s2).
Proof.
elim: s1 s2 m1 n1=> [s2 m1 n1 Hn1 Hn2|a s1 IHs1 s2 m1 n1 /eqP Hm1 /eqP Hn1].
by rewrite /block_mx -Hn1 -Hn2 !row_thin_mx col_flat_mx.
case:m1 Hm1 IHs1=> // m1 Hm1 IHs1; case:n1 Hn1 IHs1=> // n1 Hn1 IHs1.
rewrite diag_mx_seq_cons IHs1; apply/eqP=> //; rewrite diag_mx_seq_cons.
by rewrite -row_mx0 -col_mx0 block_mxA castmx_id row_mx0 col_mx0.
Qed.


(* Lemma diag_mx_seq_flatten (s : seq (seq R)) : *)
  

(*   let s' := *)
(*    [seq existTmx (diag_mx_seq (size x).-1.+1 (size x).-1.+1 x) |  x <- s] in *)
(*   (forall l, l \in s -> l != [::]) -> *)
(*   diag_mx_seq (size_sum s').+1 (size_sum s').+1 (flatten s) = diag_block_mx s'. *)
(* Proof. *)
(* elim: s=> /= [|a []]; first by rewrite diag_mx_seq_nil. *)
(*   by   rewrite /size_sum /= cats0 . *)
(* move=> b l; rewrite map_cons /= => IH Hl. *)
(* rewrite -IH -?diag_mx_seq_cat // ?prednK // ?lt0n ?size_eq0. *)
(*     by apply: Hl; rewrite mem_head. *)
(*   by apply: Hl; rewrite mem_head. *)
(* by move=> s' Hs'; apply: Hl; rewrite mem_behead. *)
(* Qed. *)

Lemma diag_mx_seq_take n (s: seq R) :
  diag_mx_seq n n (take n s) = diag_mx_seq n n s.
Proof.
by apply/matrixP=> i j; rewrite !mxE nth_take.
Qed.

End diag_mx_seq.

Section diag_mx_seq_comRingType.


Variable R : comRingType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma det_diag_mx_seq_truncated m (s : seq R) :
  \det (diag_mx_seq m m s) = (\prod_(i <- take m s) i) *+ (m <= size s).
Proof.
elim: s m=> [[|m]|a l IHl [|m]]; rewrite ?det_mx00 ?leq0n ?take0 ?big_nil //.
  by rewrite diag_mx_seq_nil det0.
rewrite big_cons ltnS diag_mx_seq_cons (@det_ublock _ 1 m).
by rewrite IHl det_scalar expr1 mulrnAr.
Qed.

Lemma det_diag_mx_seq m (s : seq R) :  size s = m ->
 \det (diag_mx_seq m m s) = \prod_(i <- s) i.
Proof.
by move=> <-; rewrite det_diag_mx_seq_truncated take_size // leqnn.
Qed.


End diag_mx_seq_comRingType.