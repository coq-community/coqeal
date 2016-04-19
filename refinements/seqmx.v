From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
From mathcomp Require Import path choice fintype tuple finset bigop poly matrix mxpoly.

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

Class map_mx_of A B C D :=
  map_mx_op : (A -> B) -> C -> D.

End classes.

Typeclasses Transparent hzero_of hmul_of heq_of top_left_of usubmx_of dsubmx_of
            lsubmx_of rsubmx_of ulsubmx_of ursubmx_of dlsubmx_of drsubmx_of
            row_mx_of col_mx_of block_mx_of const_mx_of map_mx_of.

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

Variable A B : Type.

Definition seqmx {A} := seq (seq A).
Definition hseqmx {A} := fun (_ _ : nat) => @seqmx A.

Context `{zero_of A, one_of A, add_of A, opp_of A, mul_of A, eq_of A}.

Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Definition mkseqmx_ord m n (f : 'I_m -> 'I_n -> A) : seqmx :=
  let enum_n := ord_enum_eq n in
  map (fun i => map (f i) enum_n) (ord_enum_eq m).

Global Instance const_seqmx : const_mx_of A hseqmx :=
  fun m n (x : A) => nseq m (nseq n x).

Global Instance map_seqmx : map_mx_of A B seqmx seqmx :=
  fun (f : A -> B) (M : seqmx) => map (map f) M.

Definition zipwith_seqmx (f : A -> A -> A) (M N : seqmx) :=
  zipwith (zipwith f) M N.

Definition trseqmx (M : seqmx) : @seqmx A :=
  foldr (zipwith cons) (nseq (size (nth [::] M 0)) [::]) M.

Global Instance seqmx0 : hzero_of hseqmx :=
  fun m n => const_seqmx m n 0%C.

Definition scalar_seqmx m (x : A) :=
  mkseqmx_ord (fun (i j : 'I_m) => (if i == j then x else 0%C)).

Global Instance seqmx1 m : one_of seqmx := scalar_seqmx m 1%C.

Global Instance opp_seqmx : opp_of (@seqmx A) := map (map -%C).

Global Instance add_seqmx : add_of seqmx := zipwith_seqmx +%C.

(* TODO: Implement better *)
Global Instance sub_seqmx : sub_of (@seqmx A) := fun a b => (a + - b)%C.

Global Instance mul_seqmx : @hmul_of nat hseqmx :=
  fun _ n p M N =>
    let N := trseqmx N in
    if n is O then seqmx0 (size M) p else
      map (fun r => map (foldl2 (fun z x y => (x * y) + z) 0 r)%C N) M.

Global Instance scale_seqmx : scale_of A seqmx :=
  fun x M => map (map (mul_op x)) M.

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq T f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance eq_seqmx : eq_of (@seqmx A) := eq_seq (eq_seq eq_op).

Global Instance top_left_seqmx : top_left_of seqmx A :=
  fun (M : seqmx) => nth 0%C (nth [::] M 0) 0.

Global Instance usubseqmx : usubmx_of hseqmx :=
  fun m1 m2 n (M : @seqmx A) => take m1 M.

Global Instance dsubseqmx : dsubmx_of hseqmx :=
  fun m1 m2 n (M : @seqmx A) => drop m1 M.

Global Instance lsubseqmx : lsubmx_of hseqmx :=
  fun m n1 n2 (M : @seqmx A) => map (take n1) M.

Global Instance rsubseqmx : rsubmx_of hseqmx :=
  fun m n1 n2 (M : @seqmx A) => map (drop n1) M.

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
  fun m n1 n2 (M N : @seqmx A) => zipwith cat M N.

Global Instance col_seqmx : col_mx_of hseqmx :=
  fun m1 m2 n (M N : @seqmx A) => M ++ N.

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
Definition scalar_seqmx_simpl := Eval cbv in scalar_seqmx.
Parametricity scalar_seqmx_simpl.
Realizer scalar_seqmx as scalar_seqmx_R := scalar_seqmx_simpl_R.
Parametricity seqmx1.
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

Section seqmx_more_op.

Variable R : ringType.
Context (C : Type).
Context `{zero_of C, eq_of C, spec_of C R}.

Global Instance spec_seqmx m n : spec_of (@seqmx C) 'M[R]_(m, n) :=
  fun s =>
    if (s == seqmx0 m n)%C then 0 else
      matrix_of_fun matrix_key (fun (i : 'I_m) (j : 'I_n) =>
                                  (nth 0 (nth [::] (map_seqmx spec s) i) j)).

End seqmx_more_op.

Arguments spec_seqmx / : assert.

Section seqmx_theory.

Section seqmx.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oneR  : one_of R := 1%R.
Local Instance oppR  : opp_of R := -%R.
Local Instance addR  : add_of R := +%R.
Local Instance mulR  : mul_of R := *%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.
Local Instance specR : spec_of R R := spec_id.

CoInductive Rseqmx {m1 m2} (rm : nat_R m1 m2) {n1 n2} (rn : nat_R n1 n2) :
  'M[R]_(m1,n1) -> hseqmx m2 n2 -> Type :=
  Rseqmx_spec (A : 'M[R]_(m1, n1)) M of
    size M = m2
  & forall i, i < m2 -> size (nth [::] M i) = n2
  & (forall i j, (A i j = nth 0 (nth [::] M i) j)) : Rseqmx rm rn A M.

(* Definition Rord n (i : 'I_n) j := i = j :> nat. *)

Lemma ord_enum_eqE p : ord_enum_eq p = enum 'I_p.
Proof. by rewrite enumT unlock; apply:eq_pmap ; exact:insub_eqE. Qed.

Instance Rseqmx_mkseqmx_ord m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx rm rn) (matrix_of_fun matrix_key)
          (@mkseqmx_ord R m1 n1).
Proof.
rewrite refinesE=> _ M ->; constructor; rewrite -?(nat_R_eq rm) -?(nat_R_eq rn).
    by rewrite size_map ord_enum_eqE size_enum_ord.
  move=> i ltim.
  rewrite (nth_map (Ordinal ltim)) ?ord_enum_eqE ?size_enum_ord // size_map.
  by rewrite size_enum_ord.
move=> i j.
by rewrite mxE (nth_map i) ?ord_enum_eqE ?size_enum_ord // (nth_map j)
           ?size_enum_ord // !nth_ord_enum.
Qed.

Instance Rseqmx_const_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx rm rn) matrix.const_mx (const_seqmx m2 n2).
Proof.
  rewrite refinesE=> _ x ->; constructor=> [|i ltim|i j].
      by rewrite size_nseq.
    by rewrite nth_nseq ltim size_nseq.
  by rewrite -(nat_R_eq rm) -(nat_R_eq rn);
    do 2 (rewrite nth_nseq ltn_ord); rewrite mxE.
Qed.

Instance Rseqmx_0 m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn) 0 (seqmx0 m2 n2).
Proof.
rewrite refinesE; constructor=>[|i|i j]; first by rewrite size_nseq.
  by rewrite nth_nseq => ->; rewrite size_nseq.
by rewrite mxE nth_nseq -(nat_R_eq rm) ltn_ord nth_nseq -(nat_R_eq rn) ltn_ord.
Qed.

Instance Rseqmx_scalar_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (eq ==> Rseqmx rm rm) scalar_mx (scalar_seqmx m2).
Proof.
  rewrite refinesE=> _ x ->; constructor=> [|i ltim|i j].
      by rewrite size_map ord_enum_eqE size_enum_ord.
    by rewrite (nth_map (Ordinal ltim)) ?ord_enum_eqE ?size_enum_ord // size_map
               size_enum_ord.
  rewrite mxE -(nat_R_eq rm) (nth_map i) ?(nth_map j) ?ord_enum_eqE
          ?size_enum_ord // !nth_ord_enum.
  by case: (i == j).
Qed.

Instance Rseqmx_1 m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx rm rm) 1%:M (seqmx1 m2).
Proof.
  rewrite /seqmx1.
  eapply refines_apply; first exact: Rseqmx_scalar_seqmx.
  by rewrite refinesE.
Qed.

Instance Rseqmx_opp m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rseqmx rm rn) -%R -%C.
Proof.
rewrite refinesE=> ? ? [A M h1 h2 h3].
constructor=> [|i ltim|i j]; first by rewrite size_map h1.
  rewrite (nth_map [::]); last by rewrite h1.
  by rewrite size_map h2.
rewrite mxE (nth_map [::]); last by rewrite h1 -(nat_R_eq rm) ltn_ord.
rewrite (nth_map 0); first by rewrite h3.
by rewrite h2 -?(nat_R_eq rm) -?(nat_R_eq rn) ltn_ord.
Qed.


Instance Rseqmx_add m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rseqmx rm rn ==> Rseqmx rm rn) +%R +%C.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite [(_ + _)%C]zipwithE.
      by rewrite size_map size1_zip h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip ?zipwithE ?size_map ?size1_zip /=
               ?h1 ?h'1 ?h2 ?h'2 ?ltim.
  by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size1_zip ?h1 ?h'1
             -?(nat_R_eq rm) ?ltn_ord // mxE h3 h'3 zipwithE
             -[[seq _ | _ <- _]](mkseq_nth 0%C) nth_mkseq /=
             ?(nth_map (0%C, 0%C)) ?nth_zip ?size_map /= ?size1_zip ?h2 ?h'2
             -?(nat_R_eq rm) -?(nat_R_eq rn) ?ltn_ord.
Qed.

Instance Rseqmx_sub m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rseqmx rm rn ==> Rseqmx rm rn)
          (fun M N => M - N) sub_op.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite [(_ - _)%C]zipwithE.
      by rewrite size_map size1_zip ?size_map h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip ?zipwithE ?size_map ?size1_zip /=
               ?(nth_map [::]) ?size_map ?h1 ?h'1 ?h2 ?h'2 ?ltim.
  by rewrite !mxE h3 h'3 (nth_map ([::], [::])) ?zipwithE ?(nth_map (0%C, 0%C))
             ?nth_zip /= ?(nth_map [::]) ?size1_zip ?size_map ?(nth_map 0%C)
             ?h1 ?h'1 ?h2 ?h'2 -?(nat_R_eq rm) -?(nat_R_eq rn) ?ltn_ord.
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

Instance Rseqmx_mul m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
         p1 p2 (rp : nat_R p1 p2) :
  refines (Rseqmx rm rn ==> Rseqmx rn rp ==> Rseqmx rm rp)
          mulmx (@hmul_op _ _ _  m2 n2 p2).
Proof.
  case: rn=> [|k1 k2 rk];
    rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
    constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx /seqmx0.
        by rewrite size_nseq.
      by rewrite nth_nseq h1 ltim size_nseq.
    by rewrite nth_nseq h1 -(nat_R_eq rm) ltn_ord nth_nseq -(nat_R_eq rp)
               ltn_ord mxE big_ord0.
  constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx.
      by rewrite size_map.
    rewrite (nth_map [::]) ?h1 // size_map /trseqmx h'2 //.
    by rewrite size_fold ?h'1.
  rewrite (nth_map [::]) ?h1 -?(nat_R_eq rm) // (nth_map [::]) /trseqmx
          ?size_fold ?h'1 ?h'2 // -?(nat_R_eq rp) //.
  set F := (fun z x y => _).
  have ->: forall s1 s2 (t : R), (foldl2 F t s1 s2) =
    (t + \sum_(0 <= k < minn (size s1) (size s2)) s1`_k * s2`_k).
    elim=>[s2 t|t1 s1 IHs s2 t].
      by rewrite min0n big_mkord big_ord0 GRing.addr0.
    case:s2=>[|t2 s2]; first by rewrite minn0 big_mkord big_ord0 GRing.addr0.
    by rewrite /= IHs minSS big_nat_recl // /F [(_ + t)%C]addrC addrA.
  rewrite add0r big_mkord size_nth_fold ?h'1 ?h2 -?(nat_R_eq rm) //
          ?(nat_R_eq rp) // /minn if_same mxE -(nat_R_eq rk).
  apply: eq_bigr=> k _.
  by rewrite h3 h'3 nth_fold ?h'1 ?(nat_R_eq rp) // -(nat_R_eq rk).
Qed.

Instance Rseqmx_scale m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx rm rn ==> Rseqmx rm rn) *:%R *:%C.
Proof.
  rewrite refinesE=> _ x -> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite [(_ *: _)%C]/scale_seqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_map ?h1 ?h2.
  by rewrite mxE (nth_map [::]) ?(nth_map 0%C) ?h1 ?h2 ?h3 -?(nat_R_eq rm)
             -?(nat_R_eq rn).
Qed.

Lemma eq_seqE (T : Type) (f : T -> T -> bool) s1 s2 : size s1 = size s2 ->
  eq_seq f s1 s2 = all (fun xy => f xy.1 xy.2) (zip s1 s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs] [] //= x2 s2 /eqP eq_sz.
by rewrite IHs //; apply/eqP.
Qed.

Instance Rseqmx_eq m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rseqmx rm rn ==> bool_R) eqtype.eq_op eq_op.
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
    rewrite size1_zip ?nth_zip ?h2 ?h'2 //= -(nat_R_eq rn); move=> ltjn.
    rewrite -(nat_R_eq rm) in ltim.
    have := heq (Ordinal ltim) (Ordinal ltjn); rewrite h3 h'3=> ->.
    by apply/eqP.
  rewrite eq_seqE ?h1 ?h'1 //.
  move/(all_nthP ([::], [::])).
  rewrite size1_zip ?h1 ?h'1 //; move=> heq.
  apply/matrixP=> i j.
  have := heq i; rewrite -(nat_R_eq rm) ltn_ord; move/implyP; rewrite implyTb.
  rewrite nth_zip ?h1 ?h'1 //= eq_seqE ?h2 ?h'2 -?(nat_R_eq rm) //.
  move/(all_nthP (0, 0))=> /(_ j).
  rewrite nth_zip ?size1_zip ?h2 ?h'2 -?(nat_R_eq rm) //= h3 h'3 -?(nat_R_eq rn)
          (ltn_ord _) /eqR.
  move=> he.
  by apply/eqP; rewrite he.
Qed.

Instance Rseqmx_top_left_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (Rseqmx (nat_R_S_R rm) (nat_R_S_R rm) ==> eq)
          (fun M => M ord0 ord0) top_left_op.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  by rewrite /top_left_op /top_left_seqmx h3.
Qed.

Lemma if_add_eq m n : (if m < m + n then m else (m + n)%N) = m.
Proof.
  case: n=> [|?]; first by rewrite addn0 ltnn.
  by rewrite ifT // -addn1 leq_add.
Qed.

Instance Rseqmx_usubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (addn_R rm1 rm2) rn ==> Rseqmx rm1 rn)
          (@matrix.usubmx R m11 m21 n1) (@usubseqmx R m12 m22 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /usubseqmx.
      by rewrite size_take h1 if_add_eq.
    by rewrite nth_take ?h2 ?ltn_addr.
  by rewrite mxE nth_take ?h3 -?(nat_R_eq rm1).
Qed.

Instance Rseqmx_dsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (addn_R rm1 rm2) rn ==> Rseqmx rm2 rn)
          (@matrix.dsubmx R m11 m21 n1) (@dsubseqmx R m12 m22 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /dsubseqmx.
      by rewrite size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite nth_drop h2 ?ltn_add2l.
  by rewrite mxE nth_drop h3 (nat_R_eq rm1).
Qed.

Instance Rseqmx_lsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12 (rn1 : nat_R n11 n12)
         n21 n22 (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm (addn_R rn1 rn2) ==> Rseqmx rm rn1)
          (@matrix.lsubmx R m1 n11 n21) (@lsubseqmx R m2 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite /lsubseqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_take ?h1 ?h2 // if_add_eq.
  by rewrite mxE h3 (nth_map [::]) ?nth_take ?h1 -?(nat_R_eq rn1)
             -?(nat_R_eq rm).
Qed.

Instance Rseqmx_rsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12 (rn1 : nat_R n11 n12)
         n21 n22 (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm (addn_R rn1 rn2) ==> Rseqmx rm rn2)
          (@matrix.rsubmx R m1 n11 n21) (@rsubseqmx R m2 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim|i j]; rewrite /rsubseqmx.
      by rewrite size_map.
    by rewrite (nth_map [::]) ?size_drop ?h1 ?h2 // addnC -addnBA ?subnn ?addn0.
  by rewrite mxE h3 (nth_map [::]) ?nth_drop ?h1 -?(nat_R_eq rm)
             ?(nat_R_eq rn1).
Qed.

Instance Rseqmx_ulsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm1 rn1)
          (@matrix.ulsubmx R m11 m21 n11 n21) (@ulsubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /ulsubseqmx /lsubseqmx /usubseqmx.
      by rewrite size_map size_take h1 if_add_eq.
    by rewrite (nth_map [::]) size_take ?nth_take ?h1 ?h2 ?if_add_eq ?ltn_addr.
  by rewrite !mxE h3 (nth_map [::]) ?size_take ?h1 ?if_add_eq ?nth_take
             -?(nat_R_eq rm1) -?(nat_R_eq rn1).
Qed.

Instance Rseqmx_ursubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm1 rn2)
          (@matrix.ursubmx R m11 m21 n11 n21) (@ursubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /ursubseqmx /rsubseqmx /usubseqmx.
      by rewrite size_map size_take h1 if_add_eq.
    by rewrite (nth_map [::]) ?size_take ?size_drop ?nth_take ?h1 ?h2 ?if_add_eq
               ?ltn_addr // addnC -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_drop ?size_take ?nth_take ?h1
             ?if_add_eq -?(nat_R_eq rm1) ?(nat_R_eq rn1).
Qed.

Instance Rseqmx_dlsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm2 rn1)
          (@matrix.dlsubmx R m11 m21 n11 n21) (@dlsubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /dlsubseqmx /lsubseqmx /dsubseqmx.
      by rewrite size_map size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite (nth_map [::]) ?size_take ?nth_drop ?size_drop ?h1 ?h2 ?if_add_eq
               ?ltn_add2l // addnC -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_take ?nth_drop ?size_drop ?h1
             -?(nat_R_eq rn1) -?(nat_R_eq rm1) // -(nat_R_eq rm2) addnC -addnBA
             ?subnn ?addn0.
Qed.

Instance Rseqmx_drsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2) ==> Rseqmx rm2 rn2)
          (@matrix.drsubmx R m11 m21 n11 n21) (@drsubseqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  constructor=> [|i ltim12|i j]; rewrite /drsubseqmx /rsubseqmx /dsubseqmx.
      by rewrite size_map size_drop h1 addnC -addnBA ?subnn ?addn0.
    by rewrite (nth_map [::]) size_drop ?nth_drop ?h1 ?h2 ?ltn_add2l // addnC
               -addnBA ?subnn ?addn0.
  by rewrite !mxE h3 (nth_map [::]) ?nth_drop ?size_drop ?h1 -?(nat_R_eq rm1)
             -?(nat_R_eq rn1) // addnC -addnBA ?subnn ?addn0 -?(nat_R_eq rm2).
Qed.

Instance Rseqmx_row_seqmx m1 m2 (rm : nat_R m1 m2) n11 n12 (rn1 : nat_R n11 n12)
         n21 n22 (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm rn1 ==> Rseqmx rm rn2 ==> Rseqmx rm (addn_R rn1 rn2))
          (@matrix.row_mx R m1 n11 n21) (@row_seqmx R m2 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite /row_seqmx zipwithE.
      by rewrite size_map size1_zip h1 ?h'1.
    by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size_cat ?size1_zip ?h1 ?h'1
               ?h2 ?h'2.
  rewrite mxE (nth_map ([::], [::])) ?nth_zip /= ?nth_cat ?size1_zip ?h1 ?h'1
          ?h2 ?h'2 //.
  case: (splitP j)=> k hk; rewrite ?(h3, h'3) hk -?(nat_R_eq rn1).
        by rewrite ltn_ord.
      rewrite ifN; first by rewrite addnC -addnBA ?subnn ?addn0.
      by rewrite ltnNge leq_addr.
    by rewrite -(nat_R_eq rm).
  by rewrite -(nat_R_eq rm).
Qed.

Instance Rseqmx_col_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm1 rn ==> Rseqmx rm2 rn ==> Rseqmx (addn_R rm1 rm2) rn)
          (@matrix.col_mx R m11 m21 n1) (@col_seqmx R m12 m22 n2).
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim12|i j]; rewrite /col_seqmx.
      by rewrite size_cat h1 h'1.
    rewrite nth_cat h1 -(nat_R_eq rm1); case: (ltnP i m11)=> [ltim1|leqm1i];
      rewrite ?(h2, h'2) -?(nat_R_eq rm1) //.
    by rewrite -subn_gt0 subnBA // addnC subn_gt0 (nat_R_eq rm1).
  rewrite mxE nth_cat h1.
  case: (splitP i)=> k hk; rewrite ?(h3, h'3) hk -(nat_R_eq rm1).
    by rewrite ltn_ord.
  rewrite ifN; last by rewrite ltnNge leq_addr.
  by rewrite addnC -addnBA ?subnn ?addn0.
Qed.

Instance Rseqmx_block_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
         (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
         (rn2 : nat_R n21 n22) :
  refines (Rseqmx rm1 rn1 ==> Rseqmx rm1 rn2 ==> Rseqmx rm2 rn1 ==>
                  Rseqmx rm2 rn2 ==> Rseqmx (addn_R rm1 rm2) (addn_R rn1 rn2))
          (@matrix.block_mx R m11 m21 n11 n21) (@block_seqmx R m12 m22 n12 n22).
Proof.
  rewrite refinesE=> _ _ [M1 sM1 h11 h21 h31] _ _ [M2 sM2 h12 h22 h32]
                     _ _ [M3 sM3 h13 h23 h33] _ _ [M4 sM4 h14 h24 h34].
  constructor=> [|i ltim12|i j]; rewrite /block_seqmx /col_seqmx /row_seqmx.
      by rewrite !zipwithE size_cat !size_map !size1_zip ?h11 ?h12 ?h13 ?h14.
    rewrite !zipwithE nth_cat size_map size1_zip ?h11 ?h12 // -(nat_R_eq rm1).
     case: (ltnP i m11)=> [ltim1|leqm1i];
     by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size1_zip ?size_cat
                ?(h11, h13) ?(h12, h14) ?(h21, h23) ?(h22, h24) -?(nat_R_eq rm1)
                // -subn_gt0 subnBA // addnC subn_gt0 (nat_R_eq rm1).
  rewrite mxE !zipwithE nth_cat size_map size1_zip h11 ?h12 // -(nat_R_eq rm1).
  case: (splitP i)=> k hk;
    rewrite (nth_map ([::], [::])) ?nth_zip ?size1_zip ?(h11, h13) ?(h12, h14)
            ?hk -?(nat_R_eq rm1) //= ?nth_cat ?(h21, h23) -?(nat_R_eq rm1) //
            ?mxE;
    case: (splitP j)=> l hl;
      rewrite ?(h31, h33) ?(h32, h34) ?hl -?(nat_R_eq rn1) ?ltn_ord // addnC
              -?[in _ < _]addnBA ?subnn ?addn0 -?(nat_R_eq rm2) // ?ifN ?ltnNge
              ?leq_addl //.
      by rewrite -addnBA ?subnn ?addn0.
    by rewrite -addnBA ?subnn ?addn0.
  by rewrite addnC -addnBA ?subnn ?addn0 -?addnBA ?subnn ?addn0.
Qed.

Instance Rseqmx_spec_l m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Logic.eq) spec_id spec.
Proof.
  rewrite refinesE=> _ _ [M sM h1 h2 h3].
  rewrite /spec /spec_seqmx /spec_id /spec /specR /spec_id /map_seqmx map_id_in;
    last first.
    by move=> x; rewrite map_id.
  apply/matrixP=> i j.
  case: ifP; rewrite h3 mxE //.
  rewrite /eq_op /eq_seqmx eq_seqE /seqmx0 /const_seqmx ?size_nseq ?h1
          ?(nat_R_eq rm) //.
  move/all_nthP=> heq.
  have /implyP := heq ([::], [::]) i.
  rewrite size_zip h1 size_nseq -(nat_R_eq rm) minnn ltn_ord implyTb eq_seqE
          nth_zip /= ?nth_nseq ?h1 ?h2 ?ltn_ord ?size_nseq -?(nat_R_eq rm)
          -?(nat_R_eq rn) //.
  move/all_nthP=> heq'.
  have /implyP := heq' (0, 0) j.
  rewrite size_zip h2 ?size_nseq -?(nat_R_eq rn) -?(nat_R_eq rm) ?minnn ltn_ord
          // implyTb nth_zip /= ?nth_nseq ?h2 ?size_nseq ?ltn_ord
          -?(nat_R_eq rm) ?(nat_R_eq rn) //.
  by move/eqP.
Qed.

Section seqmx_param.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, one_of C, opp_of C, add_of C, mul_of C, eq_of C}.
Context `{spec_of C R}.
Context `{!refines rAC 0%R 0%C, !refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.
Context `{!refines (rAC ==> Logic.eq) spec_id spec}.

Definition RseqmxC {m1 m2} (rm : nat_R m1 m2) {n1 n2} (rn : nat_R n1 n2) :
  'M[R]_(m1, n1) -> hseqmx m2 n2 -> Type :=
  (Rseqmx rm rn \o (list_R (list_R rAC)))%rel.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; apply: nat_Rxx. Qed.

(* Local Instance refines_refl_ord : forall m (i : 'I_m), refines nat_R i i | 999.  *)
(* Proof. ewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed. *)

(* Local Instance refines_eq_refl_nat : forall (m : nat), refines eq m m | 999.  *)
(* Proof. by rewrite refinesE. Qed. *)

Local Instance refines_ordinal_eq (m : nat) (i j : 'I_m) :
  refines (ordinal_R (nat_Rxx m)) i j -> refines eq i j.
Proof.
rewrite !refinesE=> [[m0 m1 mR i0 i1 _]].
apply: ord_inj; exact: nat_R_eq.
Qed.

Global Instance RseqmxC_mkseqmx_ord m1 m2 (rm : nat_R m1 m2) n1 n2
       (rn : nat_R n1 n2) :
  refines ((eq ==> eq ==> rAC) ==> RseqmxC rm rn)
          (matrix_of_fun matrix_key) (@mkseqmx_ord C m1 n1).
Proof. param_comp mkseqmx_ord_R. Qed.

Global Instance refine_mkseqmx_ord m n :
  refines ((eq ==> eq ==> rAC) ==> RseqmxC (nat_Rxx m) (nat_Rxx n))
          (matrix_of_fun matrix_key) (@mkseqmx_ord C m n).
Proof. exact: RseqmxC_mkseqmx_ord. Qed.

Global Instance RseqmxC_const_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2
       (rn : nat_R n1 n2) :
  refines (rAC ==> RseqmxC rm rn) (@matrix.const_mx R m1 n1)
          (const_seqmx m2 n2).
Proof. param_comp const_seqmx_R. Qed.

Global Instance refine_const_seqmx m n :
  refines (rAC ==> RseqmxC (nat_Rxx m) (nat_Rxx n)) (@matrix.const_mx R m n)
          (const_seqmx m n).
Proof. exact: RseqmxC_const_seqmx. Qed.

Global Instance RseqmxC_0 m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn) 0 (@hzero_op _ _ _ m2 n2).
Proof. param_comp seqmx0_R. Qed.

Global Instance refine_0_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n)) 0 (@hzero_op _ _ _ m n).
Proof. exact: RseqmxC_0. Qed.

Global Instance RseqmxC_scalar_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (rAC ==> RseqmxC rm rm) scalar_mx (scalar_seqmx m2).
Proof. param_comp scalar_seqmx_R. Qed.

Global Instance refine_scalar_seqmx m :
  refines (rAC ==> RseqmxC (nat_Rxx m) (nat_Rxx m)) scalar_mx (scalar_seqmx m).
Proof. exact: RseqmxC_scalar_seqmx. Qed.

Global Instance RseqmxC_1 m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rm rm) 1%:M (seqmx1 m2).
Proof. param_comp seqmx1_R. Qed.

Global Instance refine_1_seqmx m :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx m)) 1%:M (seqmx1 m).
Proof. exact: RseqmxC_1. Qed.

Global Instance RseqmxC_opp m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn) -%R -%C.
Proof. param_comp opp_seqmx_R. Qed.

Global Instance refine_opp_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n))
          -%R -%C.
Proof. exact: RseqmxC_opp. Qed.

Global Instance RseqmxC_add m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn ==> RseqmxC rm rn) +%R +%C.
Proof. param_comp add_seqmx_R. Qed.

Global Instance refine_add_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx n)) +%R +%C.
Proof. exact: RseqmxC_add. Qed.

Global Instance RseqmxC_sub m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn ==> RseqmxC rm rn)
          (fun M N => M - N) sub_op.
Proof. param_comp sub_seqmx_R. Qed.

Global Instance refine_sub_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx n))
          (fun M N => M - N) sub_op.
Proof. exact: RseqmxC_sub. Qed.

Global Instance RseqmxC_mul m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
       p1 p2 (rp : nat_R p1 p2) :
  refines (RseqmxC rm rn ==> RseqmxC rn rp ==> RseqmxC rm rp)
          mulmx (@hmul_op _ _ _  m2 n2 p2).
Proof. param_comp mul_seqmx_R. Qed.

Global Instance refine_mul_seqmx m n p :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx n) (nat_Rxx p)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx p))
          mulmx (@hmul_op _ _ _  m n p).
Proof. exact: RseqmxC_mul. Qed.

Global Instance RseqmxC_scale m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
  : refines (rAC ==> RseqmxC rm rn ==> RseqmxC rm rn) *:%R *:%C.
Proof. param_comp scale_seqmx_R. Qed.

Global Instance refine_scale_seqmx m n :
  refines (rAC ==> RseqmxC (nat_Rxx m) (nat_Rxx n) ==>
               RseqmxC (nat_Rxx m) (nat_Rxx n)) *:%R *:%C.
Proof. exact: RseqmxC_scale. Qed.

Global Instance RseqmxC_eq m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn ==> bool_R)
          eqtype.eq_op eq_op.
Proof. param_comp eq_seqmx_R. Qed.

Global Instance refine_eq_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n)
                   ==> bool_R) eqtype.eq_op eq_op.
Proof. exact: RseqmxC_eq. Qed.

Global Instance RseqmxC_top_left_seqmx m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC (nat_R_S_R rm) (nat_R_S_R rm) ==> rAC)
          (fun M => M ord0 ord0)
          (@top_left_seqmx C _).
Proof. param_comp top_left_seqmx_R. Qed.

Global Instance refine_top_left_seqmx m :
  refines (RseqmxC (nat_R_S_R (nat_Rxx m)) (nat_R_S_R (nat_Rxx m)) ==> rAC)
          (fun M => M ord0 ord0)
          (@top_left_seqmx C _).
Proof. exact: RseqmxC_top_left_seqmx. Qed.

Global Instance RseqmxC_usubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC (addn_R rm1 rm2) rn ==> RseqmxC rm1 rn)
          (@matrix.usubmx R m11 m21 n1) (@usubseqmx C m12 m22 n2).
Proof. param_comp usubseqmx_R. Qed.

Global Instance refine_usubseqmx m1 m2 n :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2)) (nat_Rxx n) ==>
                   RseqmxC (nat_Rxx m1) (nat_Rxx n))
          (@matrix.usubmx R m1 m2 n) (@usubseqmx C m1 m2 n).
Proof. exact: RseqmxC_usubseqmx. Qed.

Global Instance RseqmxC_dsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC (addn_R rm1 rm2) rn ==> RseqmxC rm2 rn)
          (@matrix.dsubmx R m11 m21 n1) (@dsubseqmx C m12 m22 n2).
Proof. param_comp dsubseqmx_R. Qed.

Global Instance refine_dsubseqmx m1 m2 n :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2)) (nat_Rxx n) ==>
                   RseqmxC (nat_Rxx m2) (nat_Rxx n))
          (@matrix.dsubmx R m1 m2 n) (@dsubseqmx C m1 m2 n).
Proof. exact: RseqmxC_dsubseqmx. Qed.

Global Instance RseqmxC_lsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12
       (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm (addn_R rn1 rn2) ==> RseqmxC rm rn1)
          (@matrix.lsubmx R m1 n11 n21) (@lsubseqmx C m2 n12 n22).
Proof. param_comp lsubseqmx_R. Qed.

Global Instance refine_lsubseqmx m n1 n2 :
  refines (RseqmxC (nat_Rxx m) (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m) (nat_Rxx n1))
          (@matrix.lsubmx R m n1 n2) (@lsubseqmx C m n1 n2).
Proof. exact: RseqmxC_lsubseqmx. Qed.

Global Instance RseqmxC_rsubseqmx m1 m2 (rm : nat_R m1 m2) n11 n12
       (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm (addn_R rn1 rn2) ==> RseqmxC rm rn2)
          (@matrix.rsubmx R m1 n11 n21) (@rsubseqmx C m2 n12 n22).
Proof. param_comp rsubseqmx_R. Qed.

Global Instance refine_rsubseqmx m n1 n2 :
  refines (RseqmxC (nat_Rxx m) (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m) (nat_Rxx n2))
          (@matrix.rsubmx R m n1 n2) (@rsubseqmx C m n1 n2).
Proof. exact: RseqmxC_rsubseqmx. Qed.

Global Instance RseqmxC_ulsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm1 rn1)
          (@matrix.ulsubmx R m11 m21 n11 n21) (@ulsubseqmx C m12 m22 n12 n22).
Proof. param_comp ulsubseqmx_R. Qed.

Global Instance refine_ulsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m1) (nat_Rxx n1))
          (@matrix.ulsubmx R m1 m2 n1 n2) (@ulsubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_ulsubseqmx. Qed.

Global Instance RseqmxC_ursubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm1 rn2)
          (@matrix.ursubmx R m11 m21 n11 n21) (@ursubseqmx C m12 m22 n12 n22).
Proof. param_comp ursubseqmx_R. Qed.

Global Instance refine_ursubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m1) (nat_Rxx n2))
          (@matrix.ursubmx R m1 m2 n1 n2) (@ursubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_ursubseqmx. Qed.

Global Instance RseqmxC_dlsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm2 rn1)
          (@matrix.dlsubmx R m11 m21 n11 n21) (@dlsubseqmx C m12 m22 n12 n22).
Proof. param_comp dlsubseqmx_R. Qed.

Global Instance refine_dlsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m2) (nat_Rxx n1))
          (@matrix.dlsubmx R m1 m2 n1 n2) (@dlsubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_dlsubseqmx. Qed.

Global Instance RseqmxC_drsubseqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2) ==> RseqmxC rm2 rn2)
          (@matrix.drsubmx R m11 m21 n11 n21) (@drsubseqmx C m12 m22 n12 n22).
Proof. param_comp drsubseqmx_R. Qed.

Global Instance refine_drsubseqmx m1 m2 n1 n2 :
  refines (RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)) ==>
                   RseqmxC (nat_Rxx m2) (nat_Rxx n2))
          (@matrix.drsubmx R m1 m2 n1 n2) (@drsubseqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_drsubseqmx. Qed.

Global Instance RseqmxC_row_seqmx m1 m2 (rm : nat_R m1 m2) n11 n12
       (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm rn1 ==> RseqmxC rm rn2 ==> RseqmxC rm (addn_R rn1 rn2))
          (@matrix.row_mx R m1 n11 n21) (@row_seqmx C m2 n12 n22).
Proof. param_comp row_seqmx_R. Qed.

Global Instance refine_row_seqmx m n1 n2 :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n1) ==> RseqmxC (nat_Rxx m) (nat_Rxx n2)
                   ==> RseqmxC (nat_Rxx m) (addn_R (nat_Rxx n1) (nat_Rxx n2)))
          (@matrix.row_mx R m n1 n2) (@row_seqmx C m n1 n2).
Proof. exact: RseqmxC_row_seqmx. Qed.

Global Instance RseqmxC_col_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm1 rn ==> RseqmxC rm2 rn ==> RseqmxC (addn_R rm1 rm2) rn)
          (@matrix.col_mx R m11 m21 n1) (@col_seqmx C m12 m22 n2).
Proof. param_comp col_seqmx_R. Qed.

Global Instance refine_col_seqmx m1 m2 n :
  refines (RseqmxC (nat_Rxx m1) (nat_Rxx n) ==> RseqmxC (nat_Rxx m2) (nat_Rxx n)
                   ==> RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2)) (nat_Rxx n))
          (@matrix.col_mx R m1 m2 n) (@col_seqmx C m1 m2 n).
Proof. exact: RseqmxC_col_seqmx. Qed.

Global Instance RseqmxC_block_seqmx m11 m12 (rm1 : nat_R m11 m12) m21 m22
       (rm2 : nat_R m21 m22) n11 n12 (rn1 : nat_R n11 n12) n21 n22
       (rn2 : nat_R n21 n22) :
  refines (RseqmxC rm1 rn1 ==> RseqmxC rm1 rn2 ==> RseqmxC rm2 rn1 ==>
           RseqmxC rm2 rn2 ==> RseqmxC (addn_R rm1 rm2) (addn_R rn1 rn2))
    (@matrix.block_mx R m11 m21 n11 n21) (@block_seqmx C m12 m22 n12 n22).
Proof. param_comp block_seqmx_R. Qed.

Global Instance refine_block_seqmx m1 m2 n1 n2 :
  refines (RseqmxC (nat_Rxx m1) (nat_Rxx n1) ==>
           RseqmxC (nat_Rxx m1) (nat_Rxx n2) ==>
           RseqmxC (nat_Rxx m2) (nat_Rxx n1) ==>
           RseqmxC (nat_Rxx m2) (nat_Rxx n2) ==>
           RseqmxC (addn_R (nat_Rxx m1) (nat_Rxx m2))
                   (addn_R (nat_Rxx n1) (nat_Rxx n2)))
    (@matrix.block_mx R m1 m2 n1 n2) (@block_seqmx C m1 m2 n1 n2).
Proof. exact: RseqmxC_block_seqmx. Qed.

Global Instance RseqmxC_spec m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> Logic.eq) spec_id spec.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE /spec /spec_seqmx /spec /specR=> l l' rl.
  have -> : forall m n, (l' == seqmx0 m n)%C = (l == seqmx0 m n)%C.
    elim: rl=> [i j|x y rx p q rp ih i j] {l l'} /=.
      by case: i.
    rewrite /eq_op /eq_seqmx /=.
    case: i=> [|i] //=.
    rewrite [eq_seq _ q _]ih.
    apply: congr2=> //=.
    elim: rx j=> [j|a b ra l l' rl ihl j] /=;
    case: j=> [|j] //=.
    by rewrite ihl [(a == _)%C]refines_eq.
  have -> : map_seqmx spec l = (map_seqmx spec l' : @seqmx R).
    elim: rl=> [|a b ra p q rp ih] //=.
    rewrite ih.
    apply: congr2=> //.
    elim: ra=> [|x y rxy s t rst ihs] //=.
    by rewrite ihs [specR _]refines_eq.
  by [].
Qed.

Global Instance refine_spec_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> Logic.eq) spec_id spec.
Proof. exact: RseqmxC_spec. Qed.

End seqmx_param.
End seqmx.

Section seqmx2.

Variable R R' : ringType.

Instance Rseqmx_map_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (eq ==> Rseqmx (R:=R) rm rn ==> Rseqmx (R:=R') rm rn)
          (fun f => @map_mx _ _ f m1 n1) map_mx_op.
Proof.
  rewrite refinesE=> _ f -> _ _ [M sM h1 h2 h3]; constructor=> [|i ltim|i j].
      by rewrite size_map.
    by rewrite (nth_map [::]) ?h1 // size_map h2.
  rewrite mxE (nth_map [::]) ?h1 -?(nat_R_eq rm) ?ltn_ord //.
  rewrite (nth_map (M i j)) ?h2 -?(nat_R_eq rm) -?(nat_R_eq rn) ?ltn_ord //.
  apply: congr1; rewrite h3 -[X in (nth (_`_ _) X _)](mkseq_nth 0) nth_mkseq //.
  by rewrite h2 -?(nat_R_eq rm) -?(nat_R_eq rn) ltn_ord.
Qed.

Section seqmx2_param.

Context (C : Type) (rAC : R -> C -> Type).
Context (D : Type) (rBD : R' -> D -> Type).

Global Instance RseqmxC_map_mx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
  : refines ((rAC ==> rBD) ==> RseqmxC rAC rm rn ==> RseqmxC rBD rm rn)
            (fun f => @map_mx _ _ f m1 n1) map_mx_op.
Proof. param_comp map_seqmx_R. Qed.

Global Instance refine_map_seqmx m n :
  refines ((rAC ==> rBD) ==> RseqmxC rAC (nat_Rxx m) (nat_Rxx n) ==>
                         RseqmxC rBD (nat_Rxx m) (nat_Rxx n))
          (fun f => @map_mx _ _ f m n) map_mx_op.
Proof. exact: RseqmxC_map_mx. Qed.

End seqmx2_param.
End seqmx2.

Section seqmx_poly.

Variable R : ringType.
Context (C : Type) (rAC : R -> C -> Type).
Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).
Variable polyX : polyC.
Context `{zero_of polyC, one_of polyC, add_of polyC, mul_of polyC,
          opp_of polyC}.
Context `{cast_of C polyC}.
Context `{!refines RpolyC 'X polyX}.
Context `{!refines RpolyC 0 0%C, !refines RpolyC 1 1%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) +%R +%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) *%R *%C}.
Context `{!refines (RpolyC ==> RpolyC) -%R -%C}.
Context `{!refines (rAC ==> RpolyC) poly.polyC cast}.

Global Instance RseqmxC_char_poly_mx m1 m2 (rm : nat_R m1 m2) :
  refines (RseqmxC rAC rm rm ==> RseqmxC RpolyC rm rm)
          (char_poly_mx (n:=m1))
          (fun s => (scalar_seqmx m2 polyX) - (map_seqmx cast s))%C.
Proof.
rewrite refinesE /char_poly_mx /sub_op /sub_seqmx=> M sM rM.
apply refinesP; eapply refines_apply.
eapply refines_apply; tc.
eapply refines_apply. tc.
eapply refines_apply; tc.
rewrite -[map_mx _ (n:=_)]/((fun f => @map_mx _ _ f _ _) _).
tc.
Qed.

Global Instance refine_char_poly_seqmx m :
  refines (RseqmxC rAC (nat_Rxx m) (nat_Rxx m)
           ==> RseqmxC RpolyC (nat_Rxx m) (nat_Rxx m))
          (char_poly_mx (n:=m))
          (fun s => (scalar_seqmx m polyX) - (map_seqmx cast s))%C.
Proof. exact: RseqmxC_char_poly_mx. Qed.

End seqmx_poly.

End seqmx_theory.

Section testmx.

From mathcomp Require Import ssrint poly.
From CoqEAL Require Import binint seqpoly.

Goal ((0 : 'M[int]_(2,2)) == 0).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (1 : 'M[int]_(2)) == 1.
rewrite [_ == _]refines_eq.
by compute.
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