Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg.
Require Import path choice fintype tuple finset ssralg bigop poly matrix.

Require Import hrel param refinements.

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

Parametricity Inductive ordinal.
Parametricity Inductive subType.
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

Instance Rseqmx_mkseqmx_ord m n :
  refines (eq ==> Rseqmx) (matrix_of_fun matrix_key) (@mkseqmx_ord R m n).
Admitted.

Instance Rseqmx_const_seqmx m n :
  refines (eq ==> Rseqmx) (@matrix.const_mx R m n) (const_seqmx m n).
Admitted.

Instance Rseqmx_map_seqmx m n :
  refines (eq ==> Rseqmx ==> Rseqmx)
     (fun (f : R -> R) => @matrix.map_mx R R f m n) map_mx_op.
Admitted.

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
  refines (Rseqmx ==> Rseqmx ==> Rseqmx) (+%R : 'M[R]_(m,n) -> 'M[R]_(m,n) -> 'M[R]_(m,n)) +%C.
Admitted.

Instance Rseqmx_sub m n :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx)
          (fun (M : 'M[R]_(m,n)) N => M - N) sub_op.
Admitted.

Instance Rseqmx_mul m n p :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx)
          (mulmx : 'M[R]_(m,n) -> 'M[R]_(n,p) -> 'M[R]_(m,p))
          (@hmul_op _ _ _  m n p).
Admitted.

Instance Rseqmx_scale m n :
  refines (eq ==> Rseqmx ==> Rseqmx)
          ( *:%R : _ -> 'M[R]_(m, n)  -> _) *:%C. 
Admitted.

Instance Rseqmx_eq m n :
  refines (Rseqmx ==> Rseqmx ==> bool_R)
            (eqtype.eq_op : 'M[R]_(m,n) -> _ -> _) eq_op.
Proof. admit. Admitted.

Instance Rseqmx_top_left_seqmx m :
  refines (Rseqmx ==> eq)
          (fun (M : 'M[R]_(1+m,1+m)) => M ord0 ord0)
          (top_left_op).
Admitted.

Instance Rseqmx_usubseqmx m1 m2 n :
  refines (Rseqmx ==> Rseqmx) (@matrix.usubmx R m1 m2 n) (@usubseqmx R m1 m2 n).
Admitted.

Instance Rseqmx_dsubseqmx m1 m2 n :
  refines (Rseqmx ==> Rseqmx) (@matrix.dsubmx R m1 m2 n) (@dsubseqmx R m1 m2 n).
Admitted.

Instance Rseqmx_lsubseqmx m n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.lsubmx R m n1 n2) (@lsubseqmx R m n1 n2).
Admitted.

Instance Rseqmx_rsubseqmx m n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.rsubmx R m n1 n2) (@rsubseqmx R m n1 n2).
Admitted.

Instance Rseqmx_ulsubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.ulsubmx R m1 m2 n1 n2) (@ulsubseqmx R m1 m2 n1 n2).
Admitted.

Instance Rseqmx_ursubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.ursubmx R m1 m2 n1 n2) (@ursubseqmx R m1 m2 n1 n2).
Admitted.

Instance Rseqmx_dlsubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.dlsubmx R m1 m2 n1 n2) (@dlsubseqmx R m1 m2 n1 n2).
Admitted.

Instance Rseqmx_drsubseqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx) (@matrix.drsubmx R m1 m2 n1 n2) (@drsubseqmx R m1 m2 n1 n2).
Admitted.

Instance Rseqmx_row_seqmx m n1 n2 :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx) (@matrix.row_mx R m n1 n2) (@row_seqmx R m n1 n2).
Admitted.

Instance Rseqmx_col_seqmx m1 m2 n :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx) (@matrix.col_mx R m1 m2 n) (@col_seqmx R m1 m2 n).
Admitted.

Instance Rseqmx_block_seqmx m1 m2 n1 n2 :
  refines (Rseqmx ==> Rseqmx ==> Rseqmx ==> Rseqmx ==> Rseqmx)
    (@matrix.block_mx R m1 m2 n1 n2) (@block_seqmx R m1 m2 n1 n2).
Admitted.

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
Proof. elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed.

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

Require Import binint ssrint poly seqpoly.

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

(* Set Typeclasses Debug. *)
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