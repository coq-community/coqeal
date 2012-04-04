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

Fixpoint size_sum_rec  m (a : 'M[R]_m.+1) (l : seq {n : nat & 'M[R]_n.+1}) :=
  match l with
   | nil=> m
   | existT p M :: tl => (m + (size_sum_rec M tl).+1)%N
 end.

Fixpoint diag_block_mx_rec m (a : 'M_m.+1) (l : seq {n : nat & 'M[R]_n.+1}) : 
  'M[R]_((size_sum_rec a l).+1) :=
  match l return 'M[R]_((size_sum_rec a l).+1) with
  | nil => a
  | existT p M :: tl => block_mx a 0 0 (diag_block_mx_rec M tl)
  end.

Fixpoint size_sum (s : seq {n : nat & 'M[R]_n.+1}) :=
   match s with
     | nil => 0%N
     | existT p M :: tl => size_sum_rec M tl
  end.

Fixpoint diag_block_mx (l : seq {n : nat & 'M[R]_n.+1}) : 
  'M[R]_((size_sum l).+1) :=
 match l with
   | nil => 0
   | existT p M :: tl => diag_block_mx_rec M tl
 end.

Definition existTmx n M := existT (fun n => 'M[R]_n.+1) n M. 

Lemma size_sum_big : forall s x, 
  (size_sum (x :: s)).+1 = (\sum_(p <- x :: s) (projT1 p).+1)%N.
Proof.
by elim=> [x|[p1 M1] l IHl [p2 M2]]; rewrite big_cons ?big_nil // -IHl.
Qed.


(** maybe we cannot reapeat  have -> ... **)
Lemma upper_triangular_diag_block (s : seq {n : nat & 'M_n.+1}) :
  (forall M, M \in s -> upper_triangular_mx (projT2 M)) ->
  upper_triangular_mx (diag_block_mx s).
Proof.
case: s=> [_|[p M] l]; first exact: upper_triangular_mx0.
elim: l p M=> [p M Hs /=|[p0 M0] l IHl p M Hs]. 
  have ->: M = (projT2 (existTmx M)) by [].
  by apply: (Hs (existTmx M)); rewrite mem_head.
apply: (@upper_triangular_block _ p.+1 _ p.+1)=> //.
  have ->: M = (projT2 (existTmx M)) by [].
  by apply: (Hs (existTmx M)); rewrite mem_head.
by apply: IHl=> M1 HM1; apply: Hs; rewrite mem_behead.
Qed.

Lemma size_sum_cat  m (a : 'M_m.+1) n (b : 'M_n.+1) s1 s2 :
 (size_sum ((existTmx a) :: s1 ++ (existTmx b) :: s2)).+1 =
((size_sum ((existTmx a) :: s1)).+1 + (size_sum ((existTmx b) :: s2)).+1)%N.
Proof. by rewrite !size_sum_big -cat_cons big_cat. Qed.

Lemma diag_block_mx_cat : forall s1 s2 m (a : 'M_m.+1) n (b : 'M_n.+1), 
  diag_block_mx (((existTmx a) :: s1) ++ ((existTmx b) :: s2)) =
  castmx (pairxx (esym (size_sum_cat a b s1 s2)))
  (block_mx (diag_block_mx ((existTmx a) :: s1)) 0 0 (diag_block_mx ((existTmx b) :: s2))).
Proof.
elim=> [s2 m a n b|[k M] l IHl s2 m a n b].
  by rewrite castmx_id.
rewrite /GRing.zero /= -(row_mx_const _ m.+1) -(col_mx_const m.+1).
rewrite (castmx_sym (@block_mxA _ _ _ _ _ _ _ a _ _ _ _ _ _ _ _)).
rewrite esymK row_mx_const col_mx_const; apply:castmx_sym.
rewrite (castmx_sym (IHl s2 _ M _ b)).
rewrite -[a](castmx_id (erefl _,erefl _)).
rewrite -(castmx_const ((size_sum_cat M b _ s2),erefl _)).
rewrite -(castmx_const (erefl _,(size_sum_cat M b _ s2))).
rewrite esymK -castmx_block ?size_sum_cat ?addnA // => eq1 eq2.
rewrite castmx_comp castmx_id.
by congr castmx; congr pair; apply: nat_irrelevance.
Qed.

Lemma cast_flatten s :  (forall x, x \in s -> x != [::]) -> 
  (size_sum [seq existTmx (diag_block_mx x) | x <- s]).+1 = 
  (size_sum (flatten s)).+1.
Proof.
elim: s => //= a [] => [IH H|b l IHl Hx].
  by rewrite cats0. 
have IHx: forall x : seq {i : nat & 'M_i.+1}, x \in b :: l -> x != [::].
  by move=> x H; apply: Hx; rewrite mem_behead.  
have {Hx}: a != [::] by apply: Hx; rewrite mem_head.
have: b != [::] by apply: IHx; rewrite mem_head.
case: a=> // [][p M] a; case: b IHx IHl=> // [][p1 M1] b IHx IHl _ _.
by rewrite size_sum_cat -IHl.
Qed.

Lemma diag_block_mx_flatten s (Hs : forall x, x \in s -> x != [::]) : 
  castmx (pairxx (cast_flatten Hs))
  (diag_block_mx (map (fun x => existTmx (diag_block_mx x)) s)) =
   diag_block_mx (flatten s).
Proof.
elim: s Hs=> [Hs| a].
  by rewrite castmx_id.
case=> /= [_ Hs|b l IHl Hs]. 
  by move: (cast_flatten Hs)=> /=; rewrite cats0=> H; rewrite castmx_id.
have IHs: forall x : seq {i : nat & 'M_i.+1}, x \in b :: l -> x != [::].
  by move=> x Hx; apply: Hs; rewrite mem_behead.
have: a != [::] by apply: Hs; rewrite mem_head.
have: b != [::] by apply: IHs; rewrite mem_head.
case: a Hs => // [][p M] a; case: b IHl IHs=> // [][p1 M1] b IHl IHs Hs _ _.
rewrite (castmx_sym (esym (IHl IHs))) /GRing.zero /=.
rewrite -[(diag_block_mx_rec M a)](castmx_id (erefl _,erefl _)).
rewrite -(castmx_const ((esym (cast_flatten IHs)),erefl _)).
rewrite -(castmx_const (erefl _,(esym (cast_flatten IHs)))).
rewrite -castmx_block -?cast_flatten // => eq1 eq2.
rewrite (castmx_sym (diag_block_mx_cat a _ M M1)).
by rewrite !castmx_comp !castmx_id.
Qed.

End diag_block_ringType.



Section diag_block_comRingType.

Variable R : comRingType.
Local Open Scope ring_scope.
Import GRing.Theory.


Lemma det_diag_block : forall (l : seq {n : nat & 'M[R]_n.+1}) x,
   \det (diag_block_mx (x :: l)) = \prod_(m <- (x :: l)) \det (projT2 m).
Proof.
elim=> [x|[n M] l Hl [p M1]]; first by rewrite big_cons big_nil mulr1.
by rewrite big_cons -Hl /= (det_lblock M1).
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

Lemma diag_mx_seq_flatten (s : seq (seq R)) :
  let s' := 
   [seq existTmx (diag_mx_seq (size x).-1.+1 (size x).-1.+1 x) |  x <- s] in
  (forall l, l \in s -> l != [::]) -> 
  diag_mx_seq (size_sum s').+1 (size_sum s').+1 (flatten s) = diag_block_mx s'.
Proof.
elim: s=> /= [|a []]; first by rewrite diag_mx_seq_nil.
  by   rewrite /size_sum /= cats0 . 
move=> b l; rewrite map_cons /= => IH Hl.
rewrite -IH -?diag_mx_seq_cat // ?prednK // ?lt0n ?size_eq0.
    by apply: Hl; rewrite mem_head.
  by apply: Hl; rewrite mem_head.
by move=> s' Hs'; apply: Hl; rewrite mem_behead.
Qed.

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