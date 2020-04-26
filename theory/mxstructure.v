(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
From mathcomp Require Import ssralg fintype perm poly mxpoly finfun tuple.
From mathcomp Require Import matrix bigop zmodp polydiv.

Require Import ssrcomplements dvdring.

(**  This file contains three parts about different structures of matrices.

     *** Lower and upper triangular matrices :
    upper_triangular_mx M == The BOOLEAN predicate that hold if
                             M is an upper traiangular matrix.
    lower_triangular_mx M == The same as upper_trianglar_mx but for
                             lower triangular matrices.
       is_triangular_mx M == M is upper or lower triangular matrix.

     *** Block diagonal matrices :
        diag_block_mx s F == A block diagonal matrix where the ith block
                             is F (nth 0 s i) i. F n i is a square matrix
                             of dimension n.+1, and s is the sequence
                             of dimension of each block minus 1.
                             It is defined by calling recursivly the
                             function block_mx.
          (size_sum s).+1 == It is the type of the matrix diag_block_mx s F.

     *** Diagonal matrices :
        diag_mx_seq m n s == A diagonal matrix of type 'M_(m,n) where
                             the ith diagonal coefficient is the ith
                             element of s.

                                                                              *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**                Triangular Matrices                          *)

Section Triangular.

Local Open Scope ring_scope.

Variable R : ringType.

Definition upper_part_mx m n (M : 'M[R]_(m,n)) :=
  \matrix_(i, j) (M i j *+ (i <= j)).

Definition lower_part_mx m n (M : 'M[R]_(m,n)) :=
  \matrix_(i, j) (M i j *+ (j <= i)).

Definition upper_triangular_mx m n (M : 'M[R]_(m,n)) := M == upper_part_mx M.

Lemma upper_triangular_mxP m n {M : 'M_(m,n)} :
  reflect (forall (i : 'I_m) (j : 'I_n), j < i -> M i j = 0)
          (upper_triangular_mx M).
Proof.
apply/(iffP idP)=> [H i j Hij|H].
  rewrite /upper_triangular_mx in H.
  by move/eqP: H=> ->; rewrite mxE leqNgt Hij.
apply/eqP/matrixP=> i j; rewrite mxE leqNgt.
have:= (H i j).
by case:(j < i)=> // ->.
Qed.

Definition lower_triangular_mx m n (M : 'M[R]_(m,n)) := M == lower_part_mx M.

Definition is_triangular_mx m n (M : 'M[R]_(m,n)) :=
   upper_triangular_mx M || lower_triangular_mx M.

Lemma upper_triangular_mx0 m n : upper_triangular_mx (0 : 'M[R]_(m,n)).
Proof. by apply/upper_triangular_mxP=> i j; rewrite mxE. Qed.

Lemma lower_triangular_mxP m n (M : 'M[R]_(m,n)) :
  lower_triangular_mx M <-> upper_triangular_mx M^T.
Proof.
rewrite /lower_triangular_mx /upper_triangular_mx.
rewrite /lower_part_mx /upper_part_mx.
split=> [/eqP ->|/eqP H]; apply/eqP.
  by apply/matrixP=> i j; rewrite !mxE; case: (i <= j).
by rewrite -[M]trmxK H; apply/matrixP=> i j; rewrite !mxE; case: (j <= i).
Qed.

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
by apply/ltn_addr/(leq_trans (ltn_ord j)).
Qed.

Lemma upper_triangular_block_mxdr :
  upper_triangular_mx (block_mx Aul Aur Adl Adr) -> n1 <= m1 ->
  upper_triangular_mx Adr.
Proof.
move=> /upper_triangular_mxP HA Hn1; apply/upper_triangular_mxP=> i j Hij.
rewrite -(HA (rshift m1 i) (rshift n1 j)) ?block_mxEdr // -addnS.
exact:leq_add.
Qed.

Lemma upper_triangular_block_mxul :
  upper_triangular_mx (block_mx Aul Aur Adl Adr) ->
  upper_triangular_mx Aul.
Proof.
move=> /upper_triangular_mxP HA; apply/upper_triangular_mxP=> i j Hij.
by rewrite -(HA (lshift m2 i) (lshift n2 j)) ?block_mxEul.
Qed.

Lemma upper_triangular_block : upper_triangular_mx Aul ->
  upper_triangular_mx Adr -> m1 <= n1 -> upper_triangular_mx (block_mx Aul 0 0 Adr).
Proof.
move=> /upper_triangular_mxP HAul /upper_triangular_mxP HAdr H.
apply/upper_triangular_mxP=> i j Hij; rewrite !mxE.
case: splitP=> k Hk; rewrite !mxE; case: splitP=> l Hl; rewrite ?mxE //.
  by apply: HAul; rewrite -Hk -Hl.
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
exact: (upper_triangular_block_mxdr HM).
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

Section SquareTriangular2.

Local Open Scope ring_scope.
Variable R : comRingType.

Lemma char_poly_triangular_mx n (M : 'M[R]_n) :
  upper_triangular_mx M -> char_poly M = \prod_i ('X - (M i i)%:P).
Proof.
move=> Ht; rewrite /char_poly det_triangular_mx ?char_poly_mx_triangular_mx //.
by apply: eq_bigr=> i _; rewrite !mxE eqxx.
Qed.

End SquareTriangular2.


(**                  Block Diagonal Matrices                *)

Section diag_block_ringType.

Variable R : ringType.
Local Open Scope ring_scope.
Import GRing.Theory.

Fixpoint size_sum_rec k (s : seq nat) : nat :=
  if s is x :: l then (k + (size_sum_rec x l).+1)%N else k.

Fixpoint diag_block_mx_rec k (s : seq nat)
 (F : (forall n, nat -> 'M[R]_n.+1)) :=
  if s is x :: l return 'M_((size_sum_rec k s).+1)
   then block_mx (F k 0%N) 0 0 (diag_block_mx_rec x l (fun n i => F n i.+1))
   else F k 0%N.

Definition size_sum s := if s is x :: l then size_sum_rec x l else 0%N.

Definition diag_block_mx s F :=
  if s is x :: l return 'M_((size_sum s).+1)
  then diag_block_mx_rec x l F else 0.

Lemma size_sum_big_cons : forall s x,
  (size_sum (x :: s)).+1 = (\sum_(k <- x :: s) k.+1)%N.
Proof.
elim=> [s|n s IHn x] /=; rewrite big_cons.
   by rewrite big_nil addn0.
by rewrite IHn.
Qed.

Lemma size_sum_big s : s != [::] ->
  (size_sum s).+1 = (\sum_(k <- s) k.+1)%N.
Proof. by case: s=> // a l _; rewrite size_sum_big_cons. Qed.

Lemma ext_block s (F1 F2 : forall n, nat -> 'M_n.+1) :
(forall i, i < size s ->
  (F1 (nth 0%N s i) i) = (F2 (nth 0%N s i) i)) ->
  diag_block_mx s F1 = diag_block_mx s F2.
Proof.
case: s=> // a l.
elim: l a F1 F2=> /= [a F1 F2 Hi|b l IHl a F1 F2 Hi].
  exact: (Hi 0%N).
set F3 := (fun n i : nat => _).
set F4 := (fun n i : nat => _).
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
by apply: IHl=> j; apply: (H j.+1).
Qed.

Lemma scalar_diag_block_mx c s (F : forall n, nat -> 'M_n.+1) :
 s != [::] -> (forall i, i < size s -> F (nth 0%N s i) i = c%:M ) ->
 diag_block_mx s F = c%:M.
Proof.
case: s => // x s _.
elim: s x F=> /= [a F Hi| b l IHl a F Hi].
  exact: (Hi 0%N).
rewrite (Hi 0%N) // IHl -?scalar_mx_block // => i Hi2.
exact: (Hi i.+1).
Qed.

Lemma diag_block_mx0 s (F : forall n, nat -> 'M_n.+1) :
 (forall i, i < size s -> F (nth 0%N s i) i = 0) <->
 diag_block_mx s F = 0.
Proof.
split; case: s=> //a l Hi.
  rewrite -(scale0r 1%:M) scalemx1.
  apply: scalar_diag_block_mx=> // i H.
  by rewrite Hi // -(scale0r 1%:M) scalemx1.
elim: l a F Hi => /= [a F Ha i|b l Ihl a F].
  by rewrite ltnS leqn0=> /eqP ->.
rewrite {3}/GRing.zero /= -(@block_mx_const _ a.+1 _ a.+1)=> Ha.
have [HFa _ _ H] := (@eq_block_mx _ _ _ _ _ (F a 0%N) _ _ _ _ _ _ _ Ha).
by case=> // i Hi; apply: (Ihl b _ H).
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

Lemma exp_diag_block_cons s F k : s != [::] ->
 (diag_block_mx s F)^+ k = diag_block_mx s (fun n i => (F n i)^+ k).
Proof.
case: s=> // x s _.
elim: s x F => //= a l IHl x F.
by rewrite -IHl exp_block_mx.
Qed.

Lemma tr_diag_block_mx s F :
  (diag_block_mx s F)^T = diag_block_mx s (fun n i => (F n i)^T).
Proof.
case: s=> [|a l] /=; first by rewrite trmx0.
elim: l a F=> //= b l IHl a F.
by rewrite (tr_block_mx (F a 0%N)) !trmx0 IHl.
Qed.

End diag_block_ringType.

Section diag_block_ringType2.

Variable R : ringType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma char_diag_block_mx s (F : forall n, nat -> 'M[R]_n.+1) :
 s != [::] -> char_poly_mx (diag_block_mx s F) =
  diag_block_mx s (fun n i => char_poly_mx (F n i)).
Proof.
case: s=> //= a l _.
elim: l a F=> //= b l IHl a F.
by rewrite -IHl -char_block_mx.
Qed.

End diag_block_ringType2.

Section diag_block_comRingType.

Variable R : comRingType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma det_diag_block s (F : forall n, nat -> 'M[R]_n.+1) :
  s != [::] ->
  \det (diag_block_mx s F) =
  \prod_(i < size s) \det (F (nth 0%N s i) i).
Proof.
case: s=> // n s _.
elim: s n F=>[n F|a l IHl n F] /=.
  by rewrite big_ord_recl big_ord0 mulr1 /=.
by rewrite (det_ublock (F n 0%N)) big_ord_recl IHl.
Qed.

Lemma horner_mx_diag_block (p : {poly R}) s F :
  s != [::] ->
  horner_mx (diag_block_mx s F) p =
  diag_block_mx s (fun n i => horner_mx (F n i) p).
Proof.
case: s=> // x s _.
elim/poly_ind: p.
  rewrite rmorph0; apply: esym; apply/diag_block_mx0=> // i _.
  by rewrite rmorph0.
move=> p c IHp.
set s1 := _ :: _.
set F1 := fun n i => _ _ (_ + _).
pose F2 := fun n i => horner_mx (F n i) p *m (F n i) + horner_mx (F n i) c%:P.
have Hi: forall i, i < size s1 -> F1 (nth 0%N s1 i) i = F2 (nth 0%N s1 i) i.
  by move=> i _; rewrite /F1 /F2 rmorphD rmorphM /= horner_mx_X.
rewrite (ext_block Hi) /F2 -add_diag_block -mulmx_diag_block.
rewrite rmorphD rmorphM /=.
rewrite horner_mx_X horner_mx_C IHp.
set F3 := fun n i => _ _ c%:P.
rewrite -(@scalar_diag_block_mx _ c (x :: s) F3) // => i Hi2.
by rewrite /F3 horner_mx_C.
Qed.

End diag_block_comRingType.

Section diag_block_comUnitRingType.

Variable R : comUnitRingType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma unitmx_diag_block s (F : forall n, nat -> 'M[R]_n.+1) :
  s != [::] ->
  (forall i, i < size s -> (F (nth 0%N s i) i) \in unitmx) ->
  (diag_block_mx s F) \in unitmx.
Proof.
case: s=> // a l _ H.
have Ha: (F a 0%N) \in unitmx by exact: (H 0%N).
elim: l a F Ha H=> //= b l IHl a F Ha H.
rewrite unitmxE (det_ublock (F a 0%N)) unitrM -!unitmxE Ha.
apply: IHl=> [|i]; first exact: (H 1%N).
exact: (H i.+1).
Qed.

Lemma invmx_diag_block s (F : forall n, nat -> 'M[R]_n.+1) :
 (diag_block_mx s F) \in unitmx ->
(diag_block_mx s F)^-1 = diag_block_mx s (fun n i => (F n i)^-1).
Proof.
case: s=> [|a l]; first by rewrite unitr0.
elim: l a F => //= b l IHl a F H.
rewrite invmx_block // IHl //.
by move: H; rewrite !unitmxE (det_ublock (F a 0%N)) unitrM; case/andP.
Qed.

End diag_block_comUnitRingType.

(**                 Diagonal Matrices                                 *)

Section diag_mx_seq.

Variable R : ringType.
Local Open Scope ring_scope.
Import GRing.Theory.

Definition diag_mx_seq m n (s : seq R) :=
   \matrix_(i < m, j < n) (s`_i *+ (i == j :> nat)).

Lemma diag_mx_seq_nil m n : diag_mx_seq m n [::] = 0.
Proof.
by apply/matrixP=> i j; rewrite !mxE nth_nil mul0rn.
Qed.

Lemma diag_mx_seq_cons m n x (s :  seq R) :
  diag_mx_seq (1 + m) (1 + n) (x :: s) =
  block_mx x%:M 0 0 (diag_mx_seq m n s).
Proof.
apply/matrixP => i j; rewrite !mxE.
by case: splitP => i' ->; rewrite mxE; case:splitP => j' ->; rewrite mxE ?ord1.
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

Lemma diag_mx_seq_block_mx m m' n n' s :
  size s <= minn m n ->
  diag_mx_seq (m + m') (n + n') s = block_mx (diag_mx_seq m n s) 0 0 0.
Proof.
move=> H; apply/matrixP=> i j; rewrite !mxE.
case: (splitP _)=> k Hk; rewrite mxE; case: (splitP _)=> l Hl; rewrite mxE Hk Hl //.
+ case: (altP (k =P (n + l)%N :> nat))=> // ->.
  rewrite nth_default ?mul0rn // (leq_trans H) //.
  by rewrite (leq_trans (geq_minr m n)) // leq_addr.
+ rewrite nth_default ?mul0rn // (leq_trans H) //.
  by rewrite (leq_trans (geq_minl m n)) // leq_addr.
+ rewrite nth_default ?mul0rn // (leq_trans H) //.
  by rewrite (leq_trans (geq_minl m n)) // leq_addr.
Qed.

Lemma diag_mx_seq_block s :
  let l := nseq (size s) 0%N in
  let F := (fun n i => (@scalar_mx _ n.+1  s`_i)) in
  diag_mx_seq (size_sum l).+1 (size_sum l).+1 s =
  diag_block_mx l F.
Proof.
case: s=> /= [|a l]; first by rewrite diag_mx_seq_nil.
have Ha: forall a, diag_mx_seq 1 1 [:: a] = a%:M.
    by move=> b; apply/matrixP=> i j; rewrite !mxE ord1.
elim: l a=> //= b l IHl a.
by rewrite -IHl -cat1s (@diag_mx_seq_cat 1 _ 1) // Ha.
Qed.

Lemma diag_block_mx_seq s (F : forall n, nat -> 'M_n.+1) :
  let n := size_sum s in
  let l := mkseq (fun i => (F 0%N i) ord0 ord0) (size s) in
  (forall i, nth 0%N s i = 0%N) ->
  diag_block_mx s F =
  diag_mx_seq n.+1 n.+1 l.
Proof.
move=> /= Hs.
set s1 := mkseq _ _.
have ->: s = nseq (size s1) 0%N.
  apply: (@eq_from_nth _ 0%N); first by rewrite size_mkseq size_nseq.
  by move=> i Hi; rewrite Hs nth_nseq size_mkseq Hi.
rewrite diag_mx_seq_block.
apply: ext_block=> i; rewrite size_nseq size_mkseq => Hi.
rewrite nth_nseq Hi nth_mkseq //.
by apply/matrixP=> k l; rewrite !mxE !ord1.
Qed.

Lemma diag_mx_seq_deltal m n (i : 'I_m) (j : 'I_n) (s : seq R) :
  delta_mx i j *m diag_mx_seq n n s = s`_j *: delta_mx i j.
Proof.
apply/matrixP=> k l; rewrite !mxE (bigD1 l) //= big1 ?addr0.
  rewrite !mxE eqxx; case Hjl: (l == j); last by rewrite andbF mulr0 mul0r.
  rewrite (eqP Hjl); case: (k == i); last by rewrite mulr0 mul0r.
  by rewrite mulr1 mul1r.
move=> p; rewrite !mxE=> /negbTE; rewrite (inj_eq (@ord_inj _))=> ->.
by rewrite mulr0.
Qed.

Lemma diag_mx_seq_deltar m n (i : 'I_m) (j : 'I_n) (s : seq R) :
  diag_mx_seq m m s *m  delta_mx i j  = s`_i *: delta_mx i j.
Proof.
apply/matrixP=> k l; rewrite !mxE (bigD1 k) //= big1 ?addr0.
  rewrite !mxE eqxx; case Hjl: (k == i); last by rewrite !mulr0.
  rewrite (eqP Hjl); case: (l == j); last by rewrite andbF !mulr0.
  by rewrite !mulr1.
move=> p; rewrite !mxE=> /negbTE; rewrite (inj_eq (@ord_inj _)) eq_sym=> ->.
by rewrite mul0r.
Qed.

Lemma diag_mx_seq_takel m n (s : seq R) :
  diag_mx_seq m n (take m s) = diag_mx_seq m n s.
Proof. by apply/matrixP=> i j; rewrite !mxE nth_take. Qed.

Lemma diag_mx_seq_taker m n (s : seq R) :
  diag_mx_seq m n (take n s) = diag_mx_seq m n s.
Proof.
apply/matrixP=> i j; rewrite !mxE.
by have [-> | //] := altP (i =P j :> nat); rewrite nth_take.
Qed.

Lemma diag_mx_seq_take_min m n (s : seq R) :
  diag_mx_seq m n (take (minn m n) s) = diag_mx_seq m n s.
Proof. by case: leqP; rewrite (diag_mx_seq_takel, diag_mx_seq_taker). Qed.

Lemma tr_diag_mx_seq m n s : (diag_mx_seq m n s)^T = diag_mx_seq n m s.
Proof.
apply/matrixP=> i j; rewrite !mxE eq_sym.
by have [-> | //] := altP (i =P j :> nat).
Qed.

Lemma mul_pid_mx_diag m n p r s :
  r <= p ->
  @pid_mx R m p r *m diag_mx_seq p n s = diag_mx_seq m n (take r s).
Proof.
move=> le_r_p; apply/matrixP=> i j; rewrite !mxE.
have [le_p_i | lt_i_p] := leqP p i.
  rewrite big1; last first.
    by move=> k _; rewrite !mxE eqn_leq leqNgt (leq_trans (ltn_ord k)) // mul0r.
  rewrite nth_default ?mul0rn // size_take.
  case: ltnP=> [_|le_s_r]; first exact: (leq_trans le_r_p).
  by apply: (leq_trans le_s_r); exact: (leq_trans le_r_p).
rewrite (bigD1 (Ordinal lt_i_p)) //= !mxE big1; last first.
  by move=> k; rewrite /eq_op /= => neq_k_i; rewrite !mxE eq_sym (negbTE neq_k_i) mul0r.
rewrite eqxx addr0 /=.
have [lt_i_r | le_r_i] := ltnP i r; first by rewrite nth_take // mul1r.
rewrite mul0r nth_default ?mul0rn // size_take; case:ltnP=> // le_s_r.
exact: (leq_trans le_s_r).
Qed.

Lemma diag_mx_seq0 m n s : all (eq_op^~ 0) s -> diag_mx_seq m n s = 0.
Proof.
elim: s m n=> [m n _|a s ih m n] /=; first by rewrite diag_mx_seq_nil.
case/andP=> /eqP -> hA.
case: m n=> [n|m [|n]]; [by apply/matrixP=> [[]]|by apply/matrixP=> i []|].
rewrite diag_mx_seq_cons ih //; apply/matrixP=> i j. 
by do 2!(rewrite !mxE split1; case: unliftP=> * /=); rewrite mxE. 
Qed.

Lemma diag_mx_seq_eq0 m n s : size s <= minn m n -> diag_mx_seq m n s = 0 -> all (eq_op^~ 0) s.
Proof.
rewrite leq_min; case/andP=> hsn hsm.
move/matrixP=> H; apply/(all_nthP 0)=> i hi; apply/eqP.
set jn := Ordinal (leq_trans hi hsn); set jm := Ordinal (leq_trans hi hsm).
by move: (H jn jm); rewrite !mxE eqxx.
Qed.

Lemma diag_mx_seq_scale m n s (d : R) :
  d *: diag_mx_seq m n s = diag_mx_seq m n [seq d * x | x <- s].
Proof.
apply/matrixP=> i j; rewrite !mxE.
case: (i == j :> nat); last by rewrite !mulr0n mulr0.
have [hi|hl] := (ltnP i (size s)); first by rewrite (@nth_map _ 0).
by rewrite ?nth_default ?mulr0 // size_map.
Qed.

End diag_mx_seq.

Section diag_mx_seq2.

Variable R : ringType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma mul_diag_mx_pid m n p r s :
  r <= p ->
  diag_mx_seq m p s *m @pid_mx R p n r  = diag_mx_seq m n (take r s).
Proof.
move=> le_r_p; rewrite -[_ *m _]trmxK trmx_mul_rev tr_pid_mx tr_diag_mx_seq.
by rewrite mul_pid_mx_diag // tr_diag_mx_seq.
Qed.

Lemma mul_diag_mx_copid m n r s :
  minn (minn m n) (size s) <= r ->
  diag_mx_seq m n s *m @copid_mx R n r = 0.
Proof.
move=> le_s_r; apply/matrixP=> i j; rewrite !mxE big1 // => k _; rewrite !mxE.
have [eq_i_k|] := altP (i =P k :> nat); last by rewrite mul0r.
have [le_s_k|lt_k_s] := leqP (size s) k.
  by rewrite eq_i_k nth_default // mul0rn mul0r.
have -> : k < r.
  by apply: (leq_trans _ le_s_r); rewrite !leq_min lt_k_s -{1}eq_i_k !ltn_ord.
by rewrite eqE /=; case H: (k == j :> nat); rewrite subrr mulr0.
Qed.

End diag_mx_seq2.

Section diag_mx_seq_comRingType.

Variable R : comRingType.
Local Open Scope ring_scope.
Import GRing.Theory.

(* Why is this not in the ssr libraries? *)
Lemma tr_copid_mx m r : (copid_mx r)^T = @copid_mx R m r.
Proof.
apply/matrixP=> i j; rewrite !mxE eq_sym.
case: eqP=> [->|/eqP hij] //=; rewrite eq_sym.
by have -> : (i == j :> nat) = false by apply/eqP/eqP.
Qed.

Lemma mul_copid_mx_diag m n r s :
  minn (minn m n) (size s) <= r ->
  @copid_mx R n r *m diag_mx_seq n m s = 0.
Proof.
move=> le_s_r.
rewrite -[_ *m _]trmxK trmx_mul tr_diag_mx_seq tr_copid_mx.
by rewrite mul_diag_mx_copid // trmx0.
Qed.

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

Section diag_mx_idomain.

Variable R : idomainType.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma mul_mx_diag_seq_min m r (s : seq R) (A : 'M_(m, r)) (B : 'M_(r, m)) :
  all (predC1 0) s -> m <= size s ->
  A *m B = diag_mx_seq _ _ s -> m <= r.
Proof.
move=> neq0_s le_m_s ABd; rewrite leqNgt; apply/negP=> /subnKC; rewrite addSnnS.
move: (_ - _)%N => m' def_m; move: le_m_s ABd; rewrite -{m}def_m in A B *.
rewrite -(vsubmxK A) -(hsubmxK B) mul_col_row => le_m_s.
have lt_r_s: r < size s.
  by move: le_m_s; rewrite addnS; apply:leq_ltn_trans; exact: leq_addr.
rewrite -[s](cat_take_drop r) diag_mx_seq_cat ?size_take ?lt_r_s //.
case/eq_block_mx=> AuBld AuBr0 AdBl0 AdBrd.
have detBl0: \det (lsubmx B) = 0.
  apply/eqP/det0P; exists (nz_row (dsubmx A)).
    rewrite nz_row_eq0; apply/eqP=> Ad0; move/matrixP/(_ 0 0):AdBrd.
    rewrite Ad0 mul0mx !mxE nth_drop addn0.
    move/(all_nthP 0)/(_ r)/(_ lt_r_s): neq0_s.
    by rewrite mulr1n /= eq_sym; move/eqP.
  rewrite /nz_row; case:pickP=> /= [i|_]; last by rewrite mul0mx.
  by rewrite -row_mul AdBl0 row0.
have: \det (diag_mx_seq r r (take r s)) = 0.
  by rewrite -AuBld det_mulmx detBl0 mulr0.
rewrite det_diag_mx_seq ?size_take ?lt_r_s //; move/eqP; rewrite prodf_seq_eq0.
apply/negP; move:neq0_s; rewrite -{1}[s](cat_take_drop r) all_cat all_predC.
by case/andP.
Qed.

Lemma mul_diag_mx_seq_eq0 m n p (M : 'M[R]_(m,n)) s :
  (forall i, i < size s -> s`_i != 0) ->
  (M *m diag_mx_seq n p s == 0) -> (M *m @pid_mx R n p (size s) == 0).
Proof.
move=> s_i_eq0 /eqP /matrixP HM.
apply/eqP/matrixP=> i j; move: (HM i j); rewrite !mxE.
have [le_nj|lt_nj] := leqP n j.
  move=> _; rewrite big1 // => k _.
  by rewrite mxE ltn_eqF ?mulr0 // (leq_trans _ le_nj).
rewrite (bigD1 (Ordinal lt_nj)) // !mxE /= eqxx mulr1n.
rewrite big1 ?addr0; last first.
  move=> k; rewrite -val_eqE /= => neq_k_j.
  by rewrite mxE (negPf neq_k_j) mulr0n mulr0.
rewrite (bigD1 (Ordinal lt_nj)) // !mxE /= eqxx.
rewrite big1 ?addr0 /=; last first.
  move=> k; rewrite -val_eqE /= => neq_k_j.
  by rewrite mxE (negPf neq_k_j) mulr0n mulr0.
have [small_j|big_j] := ltnP; last by rewrite mulr0.
by move/eqP; rewrite mulf_eq0 (negPf (s_i_eq0 _ _)) ?orbF //= ?mulr1 => /eqP.
Qed.

End diag_mx_idomain.

Section diag_mx_dvdring.

Variable R : dvdRingType.

Local Open Scope ring_scope.

Lemma diag_mx_seq_filter0 m n (s : seq R) : sorted %|%R s ->
  diag_mx_seq m n [seq x <- s | x != 0] = diag_mx_seq m n s.
Proof.
elim: s m n=> // a s ih m n h_sorted.
have h_s /= := (subseq_sorted (@dvdr_trans R) (subseq_cons s a) h_sorted).
move: h_sorted; have [-> hs |an0 _] /= := eqP.
  by rewrite ih // !diag_mx_seq0 //= ?eqxx /=; apply/sorted_dvd0r.
case: m n=> [n|m [|n]]; [by apply/matrixP=> [[]]|by apply/matrixP=> i []|].
by rewrite !diag_mx_seq_cons ih.
Qed.

End diag_mx_dvdring.
