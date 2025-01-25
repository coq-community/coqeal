(** * A few operations missing in seqmx *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype bigop matrix.

From CoqEAL Require Import hrel param refinements seqmx seqpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Import Refinements.Op.

(** * Extra material about CoqEAL *)

Arguments refines A%type B%type R%rel _ _. (* Fix a scope issue with refines *)

Arguments refinesP {T T' R x y} _.

#[export] Hint Resolve nil_R : core.

Notation ord_instN := (fun _ : nat => nat) (only parsing).

Definition Rord n1 n2 (rn : nat_R n1 n2) : 'I_n1 -> ord_instN n2 -> Type :=
  fun x y => x = y :> nat.

(** [ord0] is the only value in ['I_1]. *)
Lemma ord_1_0 (i : 'I_1) : i = ord0.
Proof. by case: i => [[]] // HH; apply /eqP. Qed.

Section classes.

(** ** Definition of operational type classes *)

Class fun_of_of A I B :=
  fun_of_op : forall (m n : nat), B m n -> I m -> I n -> A.
Class row_of I B := row_op : forall (m n : nat), I m -> B m n -> B 1%N n.
Class store_of A I B :=
  store_op : forall (m n : nat), B m n -> I m -> I n -> A -> B m n.
Class trmx_of B := trmx_op : forall m n : nat, B m n -> B n m.

End classes.

#[export] Typeclasses Transparent fun_of_of row_of store_of trmx_of.

Notation "A ^T" := (trmx_op A) : hetero_computable_scope.

(** ** General definitions for seqmx *)

Section seqmx_op.

Context {A : Type}.
Context `{zero_of A}.

#[export] Instance fun_of_seqmx : fun_of_of A ord_instN hseqmx :=
  fun (_ _ : nat) M i j => nth 0%C (nth [::] M i) j.

#[export] Instance row_seqmx : row_of ord_instN (@hseqmx A) :=
  fun (_ _ : nat) i M => [:: nth [::] M i].

Fixpoint store_aux T s k (v : T) :=
  match s, k with
    | [::], _ => [::]
    | _ :: t, O => v :: t
    | h :: t, S k => h :: store_aux t k v
  end.

Fixpoint store_seqmx0 T m i j (v : T) :=
  match m, i with
    | [::], _ => [::]
    | h :: t, O => store_aux h j v :: t
    | h :: t, S i => h :: store_seqmx0 t i j v
  end.

#[export] Instance store_seqmx : store_of A ord_instN hseqmx :=
  fun (_ _ : nat) M i j v => store_seqmx0 M i j v.

#[export] Instance trmx_seqmx : trmx_of hseqmx :=
  fun m n : nat => @trseqmx A m n.

Context `{eq_of A}.

#[export] Instance heq_seqmx : heq_of (@hseqmx A) :=
  fun (_ _ : nat) => eq_seq (eq_seq eq_op).

End seqmx_op.


(** ** Refinement proofs *)

Require Import Equivalence RelationClasses Morphisms.

Section seqmx_theory.

Context {A : Type}.
Context `{!zero_of A}.

Local Instance : spec_of A A := spec_id.

Lemma Rseqmx_spec_seqmx m n (M : @seqmx A) :
  (size M == m) && all (fun r => size r == n) M ->
  Rseqmx (nat_Rxx m) (nat_Rxx n) (spec_seqmx m n M) M.
Proof.
move/andP=>[] /eqP Hm /all_nthP Hn; split=>[//||].
{ by move=> i Hi; apply/eqP /Hn; rewrite Hm. }
move=> i j; rewrite mxE.
rewrite /map_seqmx /spec /spec_of_instance_0 /spec_id /=.
by rewrite (nth_map [::]) ?Hm ?(ltn_ord i) // map_id.
Qed.

#[export] Instance Rseqmx_fun_of_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rord rm ==> Rord rn ==> eq)
    ((@fun_of_matrix A m1 n1) : matrix A m1 n1 -> ordinal m1 -> ordinal n1 -> A)
    (@fun_of_seqmx A _ m2 n2).
Proof.
rewrite refinesE => _ _ [M sM h1 h2 h3] i _ <- j _ <-.
by rewrite /fun_of_seqmx.
Qed.

#[export] Instance Rseqmx_row_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rord rm ==> Rseqmx rm rn ==> Rseqmx (S_R O_R) rn)
    (@row A m1 n1) (@row_seqmx A m2 n2).
Proof.
rewrite refinesE=> i _ <- _ _ [M sM h1 h2 h3].
rewrite /row_seqmx; constructor=> [//||i' j].
{ by case=>//= _; apply h2; rewrite -(nat_R_eq rm). }
rewrite mxE (ord_1_0 i') /=; apply h3.
Qed.

Lemma store_aux_correct n (l : seq A) (j : 'I_n) v (j' : 'I_n) : size l = n ->
  nth 0%C (store_aux l j v) j' = if j' == j then v else nth 0%C l j'.
Proof.
elim: n j j' l; [by case|]; move=> n IH j j'.
case=>// h t [Ht]; case j' => {j'}; case; case j => {j}; case=>//= j Hj j' Hj'.
rewrite /eqtype.eq_op /= eqSS; rewrite !ltnS in Hj, Hj'.
apply (IH (Ordinal Hj) (Ordinal Hj') _ Ht).
Qed.

Lemma size_store_seqmx0 s i j x :
  seq.size (@store_seqmx0 A s j i x) = seq.size s.
Proof.
elim: s j => [|a s IHs] j; first by case: j.
case: j IHs => [|j] IHs //=.
by rewrite -(IHs j).
Qed.

Lemma size_store_aux s i x : size (@store_aux A s i x) = size s.
Proof.
elim: s i => [|a s IHs] i; first by case: i.
case: i IHs => [|i] IHs //=.
by rewrite -(IHs i).
Qed.

Lemma size_nth_store_seqmx0 s i j k x :
  size (nth [::] (@store_seqmx0 A s j i x) k) = size (nth [::] s k).
Proof.
elim: s j k => [|a s IHs] j k; first by case: j.
case: j IHs => [|j] IHs //=; case: k IHs => [|k] IHs //=.
by rewrite size_store_aux.
Qed.

#[export] Instance store_ssr : store_of A ordinal (matrix A) :=
  fun m n (M : 'M[A]_(m, n)) (i : 'I_m) (j : 'I_n) v =>
  \matrix_(i', j')
    if ((nat_of_ord i' == i) && (nat_of_ord j' == j))%N then v else M i' j'.

#[export] Instance Rseqmx_store_seqmx
       m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rord rm ==> Rord rn ==> eq ==> Rseqmx rm rn)
    (@store_ssr m1 n1) (@store_seqmx A m2 n2).
Proof.
rewrite refinesE =>_ _ [M sM h1 h2 h3] i _ <- j _ <- v _ <-.
constructor=>[|i' Hi'|i' j'].
{ by rewrite size_store_seqmx0. }
{ by rewrite size_nth_store_seqmx0; apply h2. }
rewrite mxE {}h3; move: i i' sM h2 h1; rewrite -(nat_R_eq rm) -(nat_R_eq rn).
elim m1; [by case|]; move=> m IH i i'.
case=>// h t h2 [Ht]; case i' => {i'}; case.
{ case (nat_of_ord i)=>//= _.
  by rewrite store_aux_correct //; move: (h2 O erefl). }
move=> i' Hi'; case i => {i}; case=>// i Hi.
rewrite {1}/eqtype.eq_op /=; rewrite !ltnS in Hi, Hi'.
apply (IH (Ordinal Hi) (Ordinal Hi')) => //.
by move=> k Hk; move: (h2 k.+1); apply.
Qed.

Context `{eq_of A}.

#[export] Instance heq_ssr : heq_of (matrix A) :=
  fun n1 n2 a b => [forall i, [forall j, (a i j == b i j)%C]].

#[export] Instance Rseqmx_heq_op m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx rm rn ==> Rseqmx rm rn ==> bool_R)
    (@heq_ssr m1 n1) (heq_seqmx (n:=n2)).
Proof.
rewrite refinesE=> _ _ [a a' ha1 ha2 ha3] _ _ [b b' hb1 hb2 hb3].
rewrite /heq_ssr /heq_seqmx.
rewrite eq_seqE; [|by rewrite ha1 hb1].
have SzAs : seq.size (zip a' b') = m2.
{ by rewrite size1_zip ha1 // hb1. }
match goal with
 | [ |- ?R ?a ?b ] =>
   let H := fresh in
   suff H : a = b; first (rewrite H; eapply bool_Rxx =>//)
end.
apply/idP/idP.
{ move/forallP=> H1; apply/all_nthP=> i; rewrite SzAs=> Hi.
  erewrite (nth_zip [::] [::]); rewrite ?hb1 //= eq_seqE ?ha2 ?hb2 //.
  apply/all_nthP=> j.
  erewrite (nth_zip 0%C 0%C); rewrite ?ha2 ?hb2 //= size1_zip ?ha2 ?hb2 // => Hj.
  rewrite -(nat_R_eq rm) in Hi; rewrite -(nat_R_eq rn) in Hj.
  move: (H1 (Ordinal Hi)); move/forallP => H2; move: (H2 (Ordinal Hj)).
  by rewrite ha3 hb3. }
move/all_nthP=> H1; apply/forallP=> i.
have Hi : (i < m2)%N; [by rewrite -(nat_R_eq rm) ltn_ord|].
apply/forallP=> j; rewrite ha3 hb3.
move: (H1 ([::], [::]) i); rewrite size1_zip ?ha1 ?hb1 // -(nat_R_eq rm)=> H2.
move: (H2 (ltn_ord i)); rewrite nth_zip ?ha1 ?hb1 //= eq_seqE ?ha2 ?hb2 //.
move/all_nthP=>H3; move: (H3 (zero_of0, zero_of0) j).
rewrite nth_zip ?ha2 ?hb2 //=; apply.
by rewrite size1_zip ha2 ?hb2 // -(nat_R_eq rn).
Qed.

(** ** Parametricity *)

Elpi derive.param2 fun_of_of.
Elpi derive.param2 fun_of_seqmx.
Elpi derive.param2 row_of.
Elpi derive.param2 row_seqmx.
Elpi derive.param2 store_of.
Elpi derive.param2 store_aux.
Elpi derive.param2 store_seqmx0.
Elpi derive.param2 store_seqmx.
Elpi derive.param2 trmx_of.
Elpi derive.param2 trmx_seqmx.
Elpi derive.param2 heq_of.
Elpi derive.param2 heq_seqmx.

Section seqmx_param.

Context (C : Type) (rAC : A -> C -> Type).
Context `{!zero_of C, !spec_of C A}.

Context `{!eq_of C}.

Lemma RseqmxC_spec_seqmx m n (M : @seqmx C) :
  (size M == m) && all (fun r => size r == n) M ->
  (list_R (list_R rAC)) (map_seqmx spec M) M ->
  RseqmxC rAC (nat_Rxx m) (nat_Rxx n) (spec_seqmx m n M) M.
Proof.
move=> /andP [] /eqP Hm /all_nthP Hn Hc; apply refinesP.
eapply (refines_trans (b:=map_seqmx spec M)); [by tc| |].
{ rewrite refinesE; split; [by rewrite size_map| |].
  { move=> i Hi; rewrite (nth_map 0%C) ?Hm // size_map.
    by apply/eqP/Hn; rewrite Hm. }
  by move=> i j; rewrite mxE. }
by rewrite refinesE.
Qed.

Lemma nth_R_lt (T1 T2 : Type) (T_R : T1 -> T2 -> Type) x01 x02 s1 s2 :
  list_R T_R s1 s2 ->
  forall n, (n < size s1)%N -> T_R (nth x01 s1 n) (nth x02 s2 n).
Proof.
move=> Hs n; elim: n s1 s2 Hs=> [|n IH] s1 s2 Hs Hn /=.
{ by move: Hs Hn; case s1=> [//|h1 t1] Hs _; inversion Hs. }
move: Hs Hn IH; case s1=> [//|h1 t1] Hs Hn IH.
by inversion Hs; apply IH.
Qed.

Lemma RseqmxC_fun_of_seqmx m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rAC rm rn ==> Rord rm ==> Rord rn ==> rAC)
    ((@fun_of_matrix A m1 n1) : matrix A m1 n1 -> ordinal m1 -> ordinal n1 -> A)
    (@fun_of_seqmx C _ m2 n2).
Proof.
rewrite refinesE => _ a' [_ [[a a'' h1 h2 h3] ra'']] i i' ri j j' rj.
rewrite h3 /fun_of_seqmx -ri -rj.
apply nth_R_lt.
{ apply nth_R_lt=>//; rewrite h1 -(nat_R_eq rm); apply ltn_ord. }
rewrite h2 -?(nat_R_eq rm) -?(nat_R_eq rn); apply ltn_ord.
Qed.

#[export] Instance refine_fun_of_seqmx m n :
  refines (RseqmxC rAC (nat_Rxx m) (nat_Rxx n) ==> Rord (nat_Rxx m) ==> Rord (nat_Rxx n) ==> rAC)
    ((@fun_of_matrix A m n) : matrix A m n -> ordinal m -> ordinal n -> A)
    (@fun_of_seqmx C _ m n).
Proof. exact: RseqmxC_fun_of_seqmx. Qed.

#[export] Instance refine_foldl
  (T1 T2 : Type) (rT : T1 -> T2 -> Type) (R1 R2 : Type) (rR : R1 -> R2 -> Type) :
  refines ((rR ==> rT ==> rR) ==> rR ==> list_R rT ==> rR)
    (@foldl T1 R1) (@foldl T2 R2).
Proof.
rewrite refinesE=> f f' rf z z' rz s' s'' rs'.
elim: s' s'' rs' z z' rz=> [|h t IH] s'' rs' z z' rz.
{ case: s'' rs'=> [//|h' t'] rs'; inversion rs'. }
case: s'' rs'=> [|h' t'] rs' /=; [by inversion rs'|].
apply IH; [by inversion rs'|].
by apply refinesP; refines_apply; rewrite refinesE; inversion rs'.
Qed.

End seqmx_param.

End seqmx_theory.
