From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset bigop poly matrix.

From CoqEAL Require Import hrel param refinements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Refinements.Op.

Local Open Scope ring_scope.
Local Open Scope rel.

Delimit Scope hetero_computable_scope with HC.

Section classes.

Class hzero_of I B := hzero_op : forall m n : I, B m n.
Local Notation "0" := hzero_op : hetero_computable_scope.

Class hmul_of I B := hmul_op : forall m n p : I, B m n -> B n p -> B m p.
Local Notation "*m%HC" := hmul_op.
Local Notation "x *m y" := (hmul_op x y) : hetero_computable_scope.

(* Class hopp I B := hopp_op : forall m n : I, B m n -> B m n. *)
(* Local Notation "- x" := (hopp_op x) : hetero_computable_scope. *)

Class heq_of I B := heq_op : forall m n : I, B m n -> B m n -> bool.
Local Notation "x == y" := (heq_op x y) : hetero_computable_scope.

Local Open Scope nat_scope.

(* TODO: Remove this and get a better way for extracting elements *)
Class top_left_of A B := top_left_op : A -> B.

Class usubmx_of B :=
  usubmx_op : forall (m1 m2 n : nat), B (m1 + m2) n -> B m1 n.
Class dsubmx_of B :=
  dsubmx_op : forall (m1 m2 n : nat), B (m1 + m2) n -> B m2 n.
Class lsubmx_of B :=
  lsubmx_op : forall (m n1 n2 : nat), B m (n1 + n2) -> B m n1.
Class rsubmx_of B :=
  rsubmx_op : forall (m n1 n2 : nat), B m (n1 + n2) -> B m n2.
Class ulsubmx_of B :=
  ulsubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n1.
Class ursubmx_of B :=
  ursubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m1 n2.
Class dlsubmx_of B :=
  dlsubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n1.
Class drsubmx_of B :=
  drsubmx_op : forall (m1 m2 n1 n2 : nat), B (m1 + m2) (n1 + n2) -> B m2 n2.
Class row_mx_of B :=
  row_mx_op : forall (m n1 n2 : nat), B m n1 -> B m n2 -> B m (n1 + n2).
Class col_mx_of B :=
  col_mx_op : forall (m1 m2 n : nat), B m1 n -> B m2 n -> B (m1 + m2) n.
Class block_mx_of B :=
  block_mx_op : forall (m1 m2 n1 n2 : nat),
    B m1 n1 -> B m1 n2 -> B m2 n1 -> B m2 n2 -> B (m1 + m2) (n1 + n2).

Class const_mx_of A B := const_mx_op : forall (m n : nat), A -> B m n.

(* Is this really needed as a class like this? *)
Class map_mx_of A B :=
  (* map_mx : (A -> A) -> forall (m n : nat), B m n -> B m n. *)
  map_mx_op : (A -> A) -> B -> B.

End classes.

Notation "0" := hzero_op : hetero_computable_scope.
(* Notation "- x" := (hopp_op x) : hetero_computable_scope. *)
Notation "x == y" := (heq_op x y) : hetero_computable_scope.
Notation "*m%HC" := hmul_op.
Notation "x *m y" := (hmul_op x y) : hetero_computable_scope.

Section extra_seq.

Variables (T1 T2 T3 : Type) (f : T1 -> T2 -> T3).

Fixpoint zipwith (s1 : seq T1) (s2 : seq T2) :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then f x1 x2 :: zipwith s1' s2' else [::]
  else [::].

Lemma zipwithE s1 s2 : zipwith s1 s2 = [seq f x.1 x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x1 s1 ihs1] [|x2 s2] //=; rewrite ihs1. Qed.

Fixpoint foldl2 (f : T3 -> T1 -> T2 -> T3) z (s : seq T1) (t : seq T2) :=
  if s is x :: s' then
    if t is y :: t' then foldl2 f (f z x y) s' t' else z
  else z.

End extra_seq.

Parametricity zipwith.
Parametricity foldl2.

Section seqmx_op.

Variable A : Type.

Definition seqmx := seq (seq A).
Notation hseqmx := (fun (_ _ : nat) => seqmx).

Context `{zero_of A, one_of A, add_of A, opp_of A, mul_of A, eq_of A}.

Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Definition mkseqmx_ord m n (f : 'I_m -> 'I_n -> A) : seqmx :=
  let enum_n := ord_enum_eq n in
  map (fun i => map (f i) enum_n) (ord_enum_eq m).

Global Instance const_seqmx : const_mx_of A hseqmx :=
  fun m n (x : A) => nseq m (nseq n x).

Global Instance map_seqmx : map_mx_of A seqmx :=
  fun (f : A -> A) (M : seqmx) => map (map f) M.

(* Definition map_seqmx (f : A -> A) (M : seqmx) := map (map f) M. *)

Definition zipwith_seqmx (f : A -> A -> A) (M N : seqmx) :=
  zipwith (zipwith f) M N.

Definition trseqmx (M : seqmx) : seqmx :=
  foldr (zipwith cons) (nseq (size (nth [::] M 0)) [::]) M.

Global Instance seqmx0 : hzero_of hseqmx :=
  fun m n => const_seqmx m n 0%C.

(* Global Instance seqpoly1 : one_of seqpoly := [:: 1]. *)

Global Instance opp_seqmx : opp_of seqmx := map_seqmx -%C.

Global Instance add_seqmx : add_of seqmx := zipwith_seqmx +%C.

(* TODO: Implement better *)
Global Instance sub_seqmx : sub_of seqmx := fun a b => (a + - b)%C.

Global Instance mul_seqmx : @hmul_of nat hseqmx :=
  fun _ n p M N =>
    let N := trseqmx N in
    if n is O then seqmx0 (size M) p else
      map (fun r => map (foldl2 (fun z x y => (x * y) + z) 0 r)%C N) M.

Global Instance scale_seqmx : scale_of A seqmx :=
  fun x M => map_seqmx (mul_op x) M.

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq T f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance eq_seqmx : eq_of seqmx := eq_seq (eq_seq eq_op).

Global Instance top_left_seqmx : top_left_of seqmx A :=
  fun (M : seqmx) => nth 0%C (nth [::] M 0) 0.

Global Instance usubseqmx : usubmx_of hseqmx :=
  fun m1 m2 n (M : seqmx) => take m1 M.

Global Instance dsubseqmx : dsubmx_of hseqmx :=
  fun m1 m2 n (M : seqmx) => drop m1 M.

Global Instance lsubseqmx : lsubmx_of hseqmx :=
  fun m n1 n2 (M : seqmx) => map (take n1) M.

Global Instance rsubseqmx : rsubmx_of hseqmx :=
  fun m n1 n2 (M : seqmx) => map (drop n1) M.

Global Instance ulsubseqmx : ulsubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
    lsubseqmx (usubseqmx M).

Global Instance ursubseqmx : ursubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
    rsubseqmx (usubseqmx M).

Global Instance dlsubseqmx : dlsubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
  lsubseqmx (dsubseqmx M).

Global Instance drsubseqmx : drsubmx_of hseqmx :=
  fun m1 m2 n1 n2 (M : hseqmx (m1 + m2)%N (n1 + n2)%N) =>
  rsubseqmx (dsubseqmx M).

Global Instance row_seqmx : row_mx_of hseqmx :=
  fun m n1 n2 (M N : seqmx) => zipwith cat M N.

Global Instance col_seqmx : col_mx_of hseqmx :=
  fun m1 m2 n (M N : seqmx) => M ++ N.

Global Instance block_seqmx : block_mx_of hseqmx :=
  fun m1 m2 n1 n2 Aul Aur Adl Adr =>
  col_seqmx (row_seqmx Aul Aur) (row_seqmx Adl Adr).

End seqmx_op.

Parametricity eq.
Parametricity ordinal.
Parametricity subType.
Parametricity ord_enum_eq.
Parametricity mkseqmx_ord.
Parametricity const_seqmx.
Parametricity map_seqmx.
Parametricity zipwith_seqmx.
Parametricity seqmx0.
Parametricity opp_seqmx.
Parametricity add_seqmx.
Parametricity sub_seqmx.
Parametricity trseqmx.
Parametricity mul_seqmx.
Parametricity scale_seqmx.
Parametricity eq_seq.
Parametricity eq_seqmx.
Parametricity top_left_seqmx.
Parametricity usubseqmx.
Parametricity dsubseqmx.
Parametricity lsubseqmx.
Parametricity rsubseqmx.
Parametricity ulsubseqmx.
Parametricity ursubseqmx.
Parametricity dlsubseqmx.
Parametricity drsubseqmx.
Parametricity row_seqmx.
Parametricity col_seqmx.
Parametricity block_seqmx.

Section seqmx_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oppR  : opp_of R := -%R.
Local Instance addR  : add_of R := +%R.
Local Instance mulR  : mul_of R := *%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.

CoInductive Rseqmx {m n} : 'M[R]_(m,n) -> seqmx R -> Type :=
  Rseqmx_spec (A : 'M[R]_(m,n)) M of
    size M = m
  & forall i, i < m -> size (nth [::] M i) = n
  & (forall i j, (A i j = nth 0 (nth [::] M i) j)) : Rseqmx A M.

(* Definition Rord n (i : 'I_n) j := i = j :> nat. *)

Lemma ord_enum_eqE p : ord_enum_eq p = enum 'I_p.
Proof. by rewrite enumT unlock; apply:eq_pmap ; exact:insub_eqE. Qed.

Instance Rseqmx_mkseqmx_ord m n :
  refines (eq ==> Rseqmx) (matrix_of_fun matrix_key) (@mkseqmx_ord R m n).
Proof.
  rewrite refinesE=> _ M ->; constructor=> [|i ltim|i j].
      by rewrite size_map ord_enum_eqE size_enum_ord.
    rewrite (nth_map (Ordinal ltim)) ?ord_enum_eqE ?size_enum_ord // size_map.
    by rewrite size_enum_ord.
  by rewrite mxE (nth_map i) ?ord_enum_eqE ?size_enum_ord // (nth_map j)
          ?size_enum_ord // !nth_ord_enum.
Qed.

Instance Rseqmx_const_seqmx m n :
  refines (eq ==> Rseqmx) (@matrix.const_mx R m n) (const_seqmx m n).
Proof.
  rewrite refinesE=> _ x ->; constructor=> [|i ltim|i j].
      by rewrite size_nseq.
    by rewrite nth_nseq ltim size_nseq.
  by do 2 (rewrite nth_nseq ltn_ord); rewrite mxE.
Qed.

Instance Rseqmx_map_seqmx m n :
  refines (eq ==> Rseqmx ==> Rseqmx)
     (fun (f : R -> R) => @matrix.map_mx R R f m n) map_mx_op.
Proof.
  rewrite refinesE=> _ f -> _ _ [M sM h1 h2 h3]; constructor=> [|i ltim|i j].
      by rewrite size_map.
    by rewrite (nth_map [::]) ?h1 // size_map h2.
  rewrite mxE (nth_map [::]) ?h1 ?ltn_ord // (nth_map (M i j)) ?h2 ?ltn_ord //.
  apply: congr1; rewrite h3 -[X in (nth (_`_ _) X _)](mkseq_nth 0) nth_mkseq //.
  by rewrite h2 ltn_ord.
Qed.

Instance Rseqmx_0 m n :
  refines Rseqmx (0 : 'M[R]_(m,n)) (seqmx0 m n).
Proof.
rewrite refinesE; constructor=>[|i|i j]; first by rewrite size_nseq.
  by rewrite nth_nseq => ->; rewrite size_nseq.
by rewrite mxE !(nth_nseq,ltn_ord).
Qed.

Instance Rseqmx_opp m n :
  refines (Rseqmx ==> Rseqmx) (-%R : 'M[R]_(m,n) -> 'M[R]_(m,n)) -%C.
Proof.
rewrite refinesE=> ? ? [A M h1 h2 h3].
constructor; first by rewrite size_map h1.
  move=> i him.
  rewrite (nth_map [::]); last by rewrite h1.
  by rewrite size_map h2.
move=> i j.
rewrite mxE.
rewrite /opp_seqmx.
rewrite (nth_map [::]); last by rewrite h1 ltn_ord.
rewrite (nth_map 0); first by rewrite h3.
by rewrite h2 !ltn_ord.
Qed.

Instance Rseqmx_add m n :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx)
          (+%R : 'M[R]_(m,n) -> 'M[R]_(m,n) -> 'M[R]_(m,n)) +%C.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite [(_ + _)%C]zipwithE.
      by rewrite size_map size1_zip h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip ?zipwithE ?size_map ?size1_zip /=
               ?h1 ?h'1 ?h2 ?h'2 ?ltim.
  rewrite (nth_map ([::], [::])) ?nth_zip /= ?size1_zip ?h1 ?h'1 ?ltn_ord //.
  by rewrite mxE h3 h'3 zipwithE -[[seq _ | _ <- _]](mkseq_nth 0%C) nth_mkseq /=;
    rewrite ?(nth_map (0%C, 0%C)) ?nth_zip ?size_map /= ?size1_zip ?h2 ?h'2
    ?ltn_ord.
Qed.

Instance Rseqmx_sub m n :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx)
          (fun (M : 'M[R]_(m,n)) N => M - N) sub_op.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite [(_ - _)%C]zipwithE.
      by rewrite size_map size1_zip ?size_map h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip ?zipwithE ?size_map ?size1_zip /=
               ?(nth_map [::]) ?size_map ?h1 ?h'1 ?h2 ?h'2 ?ltim.
  by rewrite !mxE h3 h'3 (nth_map ([::], [::])) ?zipwithE ?(nth_map (0%C, 0%C))
             ?nth_zip /= ?(nth_map [::]) ?size1_zip ?size_map ?(nth_map 0%C)
             ?h1 ?h'1 ?h2 ?h'2 ?ltn_ord.
Qed.

Lemma minSS (p q : nat) : minn p.+1 q.+1 = (minn p q).+1.
Proof. by rewrite /minn ltnS; case:ifP. Qed.

Lemma size_fold (s : seq (seq R)) k
      (hs : forall i : nat, i < size s -> size (nth [::] s i) = k) :
  size (foldr (zipwith cons) (nseq k [::]) s) = k.
Proof.
  elim: s hs=> [_|a s ihs hs] /=; first by rewrite size_nseq.
  rewrite zipwithE size_map size1_zip ?ihs; have /= ha := hs 0%N;
    rewrite ?ha //.
  by move=> q hq; rewrite -(hs q.+1).
Qed.

Lemma size_nth_fold (s : seq (seq R)) j k (ltkj : k < j)
      (hs : forall l : nat, l < size s -> size (nth [::] s l) = j) :
  size (nth [::] (foldr (zipwith cons) (nseq j [::]) s) k) = size s.
Proof.
  elim: s hs=> [_|a s ihs hs] /=.
    by rewrite nth_nseq if_same.
  rewrite zipwithE (nth_map (0, [::])) ?nth_zip /= ?ihs // ?size1_zip
          ?size_fold; have /= ha := hs 0%N; rewrite ?ha //;
    by move=> l hl; rewrite -(hs l.+1).
Qed.

Lemma nth_fold (s : seq (seq R)) j k l (ltks : k < size s) (ltlj : l < j)
      (hs : forall l : nat, l < size s -> size (nth [::] s l) = j) :
  (nth [::] (foldr (zipwith cons) (nseq j [::]) s) l)`_k = (nth [::] s k)`_l.
Proof.
  elim: s k ltks hs=> [_ _ _|a s ihs k ltks hs] //=.
  rewrite zipwithE (nth_map (0, [::])) ?nth_zip /= ?size1_zip ?size_fold;
    have /= ha := hs 0%N; rewrite ?ha //;
    first (case: k ltks=> [|k' ltk's] //=; rewrite ?ihs //);
    by move=> q hq; rewrite -(hs q.+1).
Qed.

Instance Rseqmx_mul m n p :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx)
          (mulmx : 'M[R]_(m,n) -> 'M[R]_(n,p) -> 'M[R]_(m,p))
          (@hmul_op _ _ _  m n p).
Proof.
  case: n=> [|n];
    rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
    constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx /seqmx0.
        by rewrite size_nseq.
      by rewrite nth_nseq h1 ltim size_nseq.
    by rewrite nth_nseq h1 ltn_ord nth_nseq ltn_ord mxE big_ord0.
  constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx.
      by rewrite size_map.
    rewrite (nth_map [::]) ?h1 // size_map /trseqmx h'2 //.
    by rewrite size_fold ?h'1.
  rewrite (nth_map [::]) ?h1 // (nth_map [::]) /trseqmx ?size_fold ?h'1 ?h'2 //.
  set F := (fun z x y => _).
  have ->: forall s1 s2 (t : R), (foldl2 F t s1 s2) =
    (t + \sum_(0 <= k < minn (size s1) (size s2)) s1`_k * s2`_k).
    elim=>[s2 t|t1 s1 IHs s2 t].
      by rewrite min0n big_mkord big_ord0 GRing.addr0.
    case:s2=>[|t2 s2]; first by rewrite minn0 big_mkord big_ord0 GRing.addr0.
    by rewrite /= IHs minSS big_nat_recl // /F [(_ + t)%C]addrC addrA.
  rewrite add0r big_mkord size_nth_fold ?h'1 ?h2 // /minn if_same.
  rewrite mxE; apply: eq_bigr=> k _.
  by rewrite h3 h'3 nth_fold ?h'1.
Qed.

Instance Rseqmx_scale m n :
  refines (eq ==> Rseqmx ==> Rseqmx)
          ( *:%R : _ -> 'M[R]_(m, n)  -> _) *:%C.
Proof.
  rewrite refinesE=> _ x -> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite [(_ *: _)%C]/scale_seqmx /map_seqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_map ?h1 ?h2.
  by rewrite mxE (nth_map [::]) ?(nth_map 0%C) ?h1 ?h2 ?h3.
Qed.

Lemma eq_seqE (T : Type) (f : T -> T -> bool) s1 s2 : size s1 = size s2 ->
  eq_seq f s1 s2 = all (fun xy => f xy.1 xy.2) (zip s1 s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs] [] //= x2 s2 /eqP eq_sz.
by rewrite IHs //; apply/eqP.
Qed.

Instance Rseqmx_eq m n :
  refines (Rseqmx ==> Rseqmx ==> bool_R)
            (eqtype.eq_op : 'M[R]_(m,n) -> _ -> _) eq_op.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  suff ->: (M == N) = (eq_seq (eq_seq eqR) sM sN).
    exact: bool_Rxx.
  apply/eqP/idP=> [/matrixP heq|].
    rewrite eq_seqE ?h1 ?h'1 //.
    apply/(all_nthP ([::], [::]))=> i.
    rewrite size1_zip ?nth_zip ?h1 ?h'1 //=; move=> ltim.
    rewrite eq_seqE ?h2 ?h'2 //.
    apply/(all_nthP (0, 0))=> j.
    rewrite size1_zip ?nth_zip ?h2 ?h'2 //=; move=> ltjn.
    have := heq (Ordinal ltim) (Ordinal ltjn); rewrite h3 h'3=> ->.
    by apply/eqP.
  rewrite eq_seqE ?h1 ?h'1 //.
  move/(all_nthP ([::], [::])).
  rewrite size1_zip ?h1 ?h'1 //; move=> heq.
  apply/matrixP=> i j.
  have := (heq i (ltn_ord _)); rewrite nth_zip ?h1 ?h'1 //= eq_seqE ?h2 ?h'2 //.
  move/(all_nthP (0, 0))=> /(_ j).
  rewrite nth_zip ?size1_zip ?h2 ?h'2 //= h3 h'3 (ltn_ord _) /eqR; move=> he.
  by apply/eqP; rewrite he.
Qed.

Instance Rseqmx_top_left_seqmx m :
  refines (Rseqmx ==> eq)
          (fun (M : 'M[R]_(1+m,1+m)) => M ord0 ord0)
          (top_left_op).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  by rewrite /top_left_op /top_left_seqmx h3.
Qed.

Lemma if_add_eq m n : (if m < m + n then m else (m + n)%N) = m.
Proof.
  case: n=> [|?]; first by rewrite addn0 ltnn.
  by rewrite ifT // -addn1 leq_add.
Qed.

Instance Rseqmx_usubseqmx m1 m2 n :
  refines (Rseqmx ==> Rseqmx) (@matrix.usubmx R m1 m2 n) (@usubseqmx R m1 m2 n).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /usubseqmx.
      by rewrite size_take h1 if_add_eq.
    by rewrite nth_take ?h2 ?ltn_addr.
  by rewrite mxE nth_take ?h3.
Qed.

Instance Rseqmx_dsubseqmx m1 m2 n :
  refines (Rseqmx ==> Rseqmx) (@matrix.dsubmx R m1 m2 n) (@dsubseqmx R m1 m2 n).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /dsubseqmx.
      by rewrite size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite nth_drop h2 ?ltn_add2l.
  by rewrite mxE nth_drop h3.
Qed.

Instance Rseqmx_lsubseqmx m n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.lsubmx R m n1 n2) (@lsubseqmx R m n1 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite /lsubseqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_take ?h1 ?h2 // if_add_eq.
  by rewrite mxE h3 (nth_map [::]) ?nth_take ?h1.
Qed.

Instance Rseqmx_rsubseqmx m n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.rsubmx R m n1 n2) (@rsubseqmx R m n1 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite /rsubseqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_drop ?h1 ?h2 // addnC -addnBA ?subnn ?addn0.
  by rewrite mxE h3 (nth_map [::]) ?nth_drop ?h1.
Qed.

Instance Rseqmx_ulsubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.ulsubmx R m1 m2 n1 n2)
          (@ulsubseqmx R m1 m2 n1 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /ulsubseqmx /lsubseqmx /usubseqmx.
      by rewrite size_map size_take h1 if_add_eq.
    by rewrite (nth_map [::]) size_take ?nth_take ?h1 ?h2 ?if_add_eq ?ltn_addr.
  by rewrite !mxE h3 (nth_map [::]) ?size_take ?h1 ?if_add_eq ?nth_take.
Qed.

Instance Rseqmx_ursubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.ursubmx R m1 m2 n1 n2)
          (@ursubseqmx R m1 m2 n1 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /ursubseqmx /rsubseqmx /usubseqmx.
      by rewrite size_map size_take h1 if_add_eq.
    rewrite (nth_map [::]) ?size_take ?size_drop ?nth_take ?h1 ?h2 ?if_add_eq
            ?ltn_addr //.
    by rewrite addnC -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_drop ?size_take ?nth_take ?h1
             ?if_add_eq.
Qed.

Instance Rseqmx_dlsubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.dlsubmx R m1 m2 n1 n2)
          (@dlsubseqmx R m1 m2 n1 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /dlsubseqmx /lsubseqmx /dsubseqmx.
      by rewrite size_map size_drop h1 addnC -addnBA ?subnn ?addn0.
    rewrite (nth_map [::]) ?size_take ?nth_drop ?size_drop ?h1 ?h2 ?if_add_eq
            ?ltn_add2l //.
    by rewrite addnC -addnBA ?subnn ?addn0.
  rewrite !mxE h3 (nth_map [::]) ?nth_take ?nth_drop ?size_drop ?h1 //.
  by rewrite addnC -addnBA ?subnn ?addn0.
Qed.

Instance Rseqmx_drsubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.drsubmx R m1 m2 n1 n2)
          (@drsubseqmx R m1 m2 n1 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /drsubseqmx /rsubseqmx /dsubseqmx.
      by rewrite size_map size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite (nth_map [::]) size_drop ?nth_drop ?h1 ?h2 ?ltn_add2l // addnC
               -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_drop ?size_drop ?h1 // addnC -addnBA
     ?subnn ?addn0.
Qed.

Instance Rseqmx_row_seqmx m n1 n2 :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx) (@matrix.row_mx R m n1 n2)
          (@row_seqmx R m n1 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite /row_seqmx zipwithE.
      by rewrite size_map size1_zip h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size_cat ?size1_zip ?h1 ?h'1
               ?h2 ?h'2.
  rewrite mxE (nth_map ([::], [::])) ?nth_zip /= ?nth_cat ?size1_zip ?h1 ?h'1
          ?h2 ?h'2 //.
  by case: (splitP j)=> k hk; rewrite ?(h3, h'3) hk // addnC -addnBA ?subnn
                                      ?addn0.
Qed.

Instance Rseqmx_col_seqmx m1 m2 n :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx) (@matrix.col_mx R m1 m2 n)
          (@col_seqmx R m1 m2 n).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim12|i j]; rewrite /col_seqmx.
      by rewrite size_cat h1 h'1.
    rewrite nth_cat h1; case: (ltnP i m1)=> [ltim1|leqm1i];
      rewrite ?(h2, h'2) //.
    by rewrite -subn_gt0 subnBA // addnC subn_gt0.
  rewrite mxE nth_cat h1.
  by case: (splitP i)=> k hk; rewrite ?(h3, h'3) hk // addnC -addnBA ?subnn
                                      ?addn0.
Qed.

Instance Rseqmx_block_seqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx ==> Rseqmx ==> Rseqmx)
    (@matrix.block_mx R m1 m2 n1 n2) (@block_seqmx R m1 m2 n1 n2).
Proof.
  rewrite refinesE=> _ _ [M1 sM1 h11 h21 h31] _ _ [M2 sM2 h12 h22 h32]
                     _ _ [M3 sM3 h13 h23 h33] _ _ [M4 sM4 h14 h24 h34].
  constructor=> [|i ltim12|i j]; rewrite /block_seqmx /col_seqmx /row_seqmx.
      by rewrite !zipwithE size_cat !size_map !size1_zip ?h11 ?h12 ?h13 ?h14.
    rewrite !zipwithE nth_cat size_map size1_zip ?h11 ?h12 //.
    by case: (ltnP i m1)=> [ltim1|leqm1i];
      rewrite (nth_map ([::], [::])) ?nth_zip /= ?size1_zip ?size_cat
              ?(h11, h13) ?(h12, h14) ?(h21, h23) ?(h22, h24) //
              -subn_gt0 subnBA // addnC subn_gt0.
  rewrite mxE !zipwithE nth_cat size_map size1_zip h11 ?h12 //.
  case: (splitP i)=> k hk;
    rewrite (nth_map ([::], [::])) ?nth_zip ?size1_zip ?(h11, h13) ?(h12, h14)
            ?hk //= ?nth_cat ?(h21, h23) // ?mxE;
    case: (splitP j)=> l hl;
      rewrite ?(h31, h33) ?(h32, h34) ?hl // addnC -addnBA ?subnn ?addn0 //.
  by rewrite addnC -addnBA ?subnn ?addn0.
Qed.

Section seqmx_refines.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, opp_of C, add_of C, mul_of C, eq_of C}.
Context `{!refines rAC 0%R 0%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.

Definition RseqmxC {m n} := (@Rseqmx m n \o (list_R (list_R rAC)))%rel.

Lemma refl_nat_R : forall m, nat_R m m.
Proof. elim=> [|n]; [ exact: nat_R_O_R | exact: nat_R_S_R ]. Qed.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; apply: refl_nat_R. Qed.

(* Local Instance refines_refl_ord : forall m (i : 'I_m), refines nat_R i i | 999.  *)
(* Proof. ewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed. *)

(* Local Instance refines_eq_refl_nat : forall (m : nat), refines eq m m | 999.  *)
(* Proof. by rewrite refinesE. Qed. *)

Local Instance refines_ordinal_eq (m : nat) (i j : 'I_m) :
  refines (ordinal_R (refl_nat_R m)) i j -> refines eq i j.
Proof.
rewrite !refinesE=> [[m0 m1 mR i0 i1 _]].
apply: ord_inj; exact: nat_R_eq.
Qed.

Global Instance RseqmxC_mkseqmx_ord m n :
  refines ((eq ==> eq ==> rAC) ==> RseqmxC)
          (matrix_of_fun matrix_key) (@mkseqmx_ord C m n).
Proof. param_comp mkseqmx_ord_R. Qed.

Global Instance RseqmxC_const_seqmx m n :
  refines (rAC ==> RseqmxC) (@matrix.const_mx R m n) (const_seqmx m n).
Proof. param_comp const_seqmx_R. Qed.

Global Instance RseqmxC_0 m n :
  refines RseqmxC (0 : 'M[R]_(m,n)) (@hzero_op _ (fun _ _ => seqmx C) _ m n).
Proof. param_comp seqmx0_R. Qed.

Global Instance RseqmxC_map_mx m n :
  refines ((rAC ==> rAC) ==> RseqmxC ==> RseqmxC)
          (fun f => @matrix.map_mx R R f m n) (@map_seqmx C).
Proof. param_comp map_seqmx_R. Qed.

Global Instance RseqmxC_opp m n :
  refines (RseqmxC ==> RseqmxC) (-%R : 'M[R]_(m,n) -> 'M[R]_(m,n)) -%C.
Proof. param_comp opp_seqmx_R. Qed.

Global Instance RseqmxC_add m n :
  refines (RseqmxC ==> RseqmxC ==> RseqmxC)
          (+%R : 'M[R]_(m,n) -> 'M[R]_(m,n) -> 'M[R]_(m,n)) +%C.
Proof. param_comp add_seqmx_R. Qed.

Global Instance RseqmxC_sub m n :
  refines (RseqmxC ==> RseqmxC ==> RseqmxC)
          (fun (M : 'M[R]_(m,n)) N => M - N) sub_op.
Proof. param_comp sub_seqmx_R. Qed.

Global Instance RseqmxC_mul m n p :
  refines (RseqmxC ==> RseqmxC ==> RseqmxC)
          (mulmx : 'M[R]_(m,n) -> 'M[R]_(n,p) -> 'M[R]_(m,p))
          (@hmul_op _ _ _  m n p).
Proof. param_comp mul_seqmx_R. Qed.

Global Instance RseqmxC_scale m n :
  refines (rAC ==> RseqmxC ==> RseqmxC)
          ( *:%R : _ -> 'M[R]_(m,n)  -> _) *:%C.
Proof. param_comp scale_seqmx_R. Qed.

Global Instance RseqmxC_eq m n :
  refines (RseqmxC ==> RseqmxC ==> bool_R)
          (eqtype.eq_op : 'M[R]_(m,n) -> _ -> _) eq_op.
Proof. param_comp eq_seqmx_R. Qed.

Global Instance RseqmxC_top_left_seqmx m :
  refines (RseqmxC ==> rAC)
          (fun (M : 'M[R]_(1+m,1+m)) => M ord0 ord0)
          (@top_left_seqmx C _).
Proof. param_comp top_left_seqmx_R. Qed.

Global Instance RseqmxC_usubseqmx m1 m2 n :
  refines (RseqmxC ==> RseqmxC) (@matrix.usubmx R m1 m2 n) (@usubseqmx C m1 m2 n).
Proof. param_comp usubseqmx_R. Qed.

Global Instance RseqmxC_dsubseqmx m1 m2 n :
  refines (RseqmxC ==> RseqmxC) (@matrix.dsubmx R m1 m2 n) (@dsubseqmx C m1 m2 n).
Proof. param_comp dsubseqmx_R. Qed.

Global Instance RseqmxC_lsubseqmx m n1 n2 :
  refines (RseqmxC ==> RseqmxC) (@matrix.lsubmx R m n1 n2) (@lsubseqmx C m n1 n2).
Proof. param_comp lsubseqmx_R. Qed.

Global Instance RseqmxC_rsubseqmx m n1 n2 :
  refines (RseqmxC ==> RseqmxC) (@matrix.rsubmx R m n1 n2) (@rsubseqmx C m n1 n2).
Proof. param_comp rsubseqmx_R. Qed.

Global Instance RseqmxC_ulsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC ==> RseqmxC) (@matrix.ulsubmx R m1 m2 n1 n2) (@ulsubseqmx C m1 m2 n1 n2).
Proof. param_comp ulsubseqmx_R. Qed.

Global Instance RseqmxC_ursubseqmx m1 m2 n1 n2 :
  refines (RseqmxC ==> RseqmxC) (@matrix.ursubmx R m1 m2 n1 n2) (@ursubseqmx C m1 m2 n1 n2).
Proof. param_comp ursubseqmx_R. Qed.

Global Instance RseqmxC_dlsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC ==> RseqmxC) (@matrix.dlsubmx R m1 m2 n1 n2) (@dlsubseqmx C m1 m2 n1 n2).
Proof. param_comp dlsubseqmx_R. Qed.

Global Instance RseqmxC_drsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC ==> RseqmxC) (@matrix.drsubmx R m1 m2 n1 n2) (@drsubseqmx C m1 m2 n1 n2).
Proof. param_comp drsubseqmx_R. Qed.

Global Instance RseqmxC_row_seqmx m n1 n2 :
  refines (RseqmxC ==> RseqmxC ==> RseqmxC) (@matrix.row_mx R m n1 n2) (@row_seqmx C m n1 n2).
Proof. param_comp row_seqmx_R. Qed.

Global Instance RseqmxC_col_seqmx m1 m2 n :
  refines (RseqmxC ==> RseqmxC ==> RseqmxC) (@matrix.col_mx R m1 m2 n) (@col_seqmx C m1 m2 n).
Proof. param_comp col_seqmx_R. Qed.

Global Instance RseqmxC_block_seqmx m1 m2 n1 n2 :
  refines (RseqmxC ==> RseqmxC ==> RseqmxC ==> RseqmxC ==> RseqmxC)
    (@matrix.block_mx R m1 m2 n1 n2) (@block_seqmx C m1 m2 n1 n2).
Proof. param_comp block_seqmx_R. Qed.

End seqmx_refines.
End seqmx_theory.

Section testmx.

From mathcomp Require Import ssrint poly.
From CoqEAL Require Import binint seqpoly.

Goal ((0 : 'M[int]_(2,2)) == 0).
rewrite [_ == _]refines_eq.
by compute.
(* erewrite param_eq; last first. *)
(* eapply param_bool_eq; tc. *)
(* eapply param_apply; tc. *)
(* eapply param_apply; tc. *)
(* eapply RseqmxC_0; tc. *)
(* eapply RseqmxC_0; tc. *)
(* by compute. *)
Abort.

Goal ((- 0 : 'M[int]_(2,2)) == - - - 0).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal ((- 0 : 'M[{poly int}]_(2,2)) == - - - 0).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Definition M3 : 'M[int]_(2,2) := \matrix_(i,j < 2) 3%:Z.
Definition Mn3 : 'M[int]_(2,2) := \matrix_(i,j < 2) - 3%:Z.
Definition M6 : 'M[int]_(2,2) := \matrix_(i,j < 2) 6%:Z.

(* This works... *)
Instance refines_fun A B C D (R : A -> B -> Type) (Q : C -> D -> Type)
  a b `{!refines Q a b} : refines (R ==> Q) (fun _ => a) (fun _ => b).
Proof. by rewrite refinesE => ? ? ?; apply: refinesP. Qed.

Goal (- - M3 == M3).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (- M3 == Mn3).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (M3 - M3 == 0).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (M3 + M3 == M6).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Definition Mp : 'M[{poly {poly int}}]_(2,2) :=
  \matrix_(i,j < 2) (Poly [:: Poly [:: 3%:Z; 0; 1]; 0]).

Goal (Mp + -Mp == 0).
rewrite [_ == _]refines_eq /=.
by compute.
Abort.

Goal (Mp *m 0 == 0 :> 'M[_]_(2,2)).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Definition M := \matrix_(i,j < 2) 1%num%:Z.
Definition N := \matrix_(i,j < 2) 2%num%:Z.
Definition P := \matrix_(i,j < 2) 14%num%:Z.

Goal (M + N + M + N + M + N + N + M + N) *m
   (M + N + M + N + M + N + N + M + N) =
  (P *m M + P *m N + P *m M + P *m N +
   P *m M + P *m N + P *m N + P *m M + P *m N).
Proof.
apply/eqP.
Time rewrite [_ == _]refines_eq.
by compute.
Abort.

End testmx.