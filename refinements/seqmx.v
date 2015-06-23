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

(* Class hopp I B := hopp_op : forall m n : I, B m n -> B m n. *)
(* Local Notation "- x" := (hopp_op x) : hetero_computable_scope. *)

Class heq_of I B := heq_op : forall m n : I, B m n -> B m n -> bool.
Local Notation "x == y" := (heq_op x y) : hetero_computable_scope.

End classes.

Notation "0" := hzero_op : hetero_computable_scope.
(* Notation "- x" := (hopp_op x) : hetero_computable_scope. *)
Notation "x == y" := (heq_op x y) : hetero_computable_scope.

Section zipwith.
Variables (T1 T2 R : Type) (f : T1 -> T2 -> R).

Fixpoint zipwith (s1 : seq T1) (s2 : seq T2) :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then f x1 x2 :: zipwith s1' s2' else [::]
  else [::].

Lemma zipwithE s1 s2 : zipwith s1 s2 = [seq f x.1 x.2 | x <- zip s1 s2].
Proof. by elim: s1 s2 => [|x1 s1 ihs1] [|x2 s2] //=; rewrite ihs1. Qed.

End zipwith.

Parametricity zipwith.

Section seqmx_op.

Variable A : Type.

Definition seqmx := seq (seq A).
Notation hseqmx := (fun (_ _ : nat) => seqmx).

Context `{zero_of A, one_of A, add_of A, opp_of A, eq_of A}.

Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Definition mkseqmx_ord m n (f : 'I_m -> 'I_n -> A) : seqmx :=
  let enum_n := ord_enum_eq n in
  map (fun i => map (f i) enum_n) (ord_enum_eq m).

Definition const_seqmx m n (x : A) := nseq m (nseq n x).
Definition map_seqmx (f : A -> A) (M : seqmx) := map (map f) M. 

Definition zipwith_seqmx (f : A -> A -> A) (M N : seqmx) :=
  zipwith (zipwith f) M N.

Global Instance seqmx0 : hzero_of hseqmx := fun m n => const_seqmx m n 0%C.
(* Global Instance seqpoly1 : one_of seqpoly := [:: 1]. *)

Global Instance opp_seqmx : opp_of seqmx := map_seqmx -%C.

Global Instance add_seqmx : add_of seqmx := zipwith_seqmx +%C.

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq T f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance eq_seqmx : eq_of seqmx := eq_seq (eq_seq eq_op).

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
Parametricity eq_seq.
Parametricity eq_seqmx.

Section seqmx_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oppR  : opp_of R := -%R.
Local Instance addR  : add_of R := +%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.

CoInductive Rseqmx {m n} : 'M[R]_(m,n) -> seqmx R -> Type :=
  Rseqmx_spec (A : 'M[R]_(m,n)) M of
    size M = m
  & forall i, i < m -> size (nth [::] M i) = n
  & (forall i j, (A i j = nth 0 (nth [::] M i) j)) : Rseqmx A M.

(* Definition Rord n (i : 'I_n) j := i = j :> nat. *)

Instance Rseqmx_mkseqmx_ord m n :
  refines (Logic.eq ==> Rseqmx) (matrix_of_fun matrix_key) (@mkseqmx_ord R m n).
Admitted.

Instance Rseqmx_0 m n :
  refines Rseqmx (0 : 'M[R]_(m,n)) (@hzero_op _ (fun _ _ => seqmx R) _ m n).
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

Instance Rseqmx_eq m n :
  refines (Rseqmx ==> Rseqmx ==> bool_R)
            (eqtype.eq_op : 'M[R]_(m,n) -> _ -> _) eq_op.
Proof. admit. Admitted.

Section seqmx_param.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, opp_of C, add_of C, eq_of C}.
Context `{!refines rAC 0%R 0%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.

Definition RseqmxC {m n} := (@Rseqmx m n \o (list_R (list_R rAC)))%rel.

Lemma refl_nat_R : forall m, nat_R m m.
Proof. elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; apply: refl_nat_R. Qed.

(* Local Instance refines_refl_ord : forall m (i : 'I_m), refines nat_R i i | 999.  *)
(* Proof. ewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed. *)

(* Local Instance refines_eq_refl_nat : forall (m : nat), refines Logic.eq m m | 999.  *)
(* Proof. by rewrite refinesE. Qed. *)

Local Instance refines_ordinal_eq (m : nat) (i j : 'I_m) :
  refines (ordinal_R (refl_nat_R m)) i j -> refines eq i j.
Proof.
rewrite !refinesE=> [[m0 m1 mR i0 i1 _]].
apply: ord_inj; exact: nat_R_eq.
Qed.

Global Instance RseqmxC_mkseqmx_ord m n :
  refines ((Logic.eq ==> Logic.eq ==> rAC) ==> RseqmxC)
          (matrix_of_fun matrix_key) (@mkseqmx_ord C m n).
Proof. param_comp mkseqmx_ord_R. Qed.

Global Instance RseqmxC_0 m n :
  refines RseqmxC (0 : 'M[R]_(m,n)) (@hzero_op _ (fun _ _ => seqmx C) _ m n).
Proof. param_comp seqmx0_R. Qed.

Global Instance RseqmxC_opp m n :
  refines (RseqmxC ==> RseqmxC) (-%R : 'M[R]_(m,n) -> 'M[R]_(m,n)) -%C.
Proof. param_comp opp_seqmx_R. Qed.

Global Instance RseqmxC_add m n :
  refines (RseqmxC ==> RseqmxC ==> RseqmxC) (+%R : 'M[R]_(m,n) -> 'M[R]_(m,n) -> 'M[R]_(m,n)) +%C.
Proof. param_comp add_seqmx_R. Qed.

Global Instance RseqmxC_eq m n :
  refines (RseqmxC ==> RseqmxC ==> bool_R)
          (eqtype.eq_op : 'M[R]_(m,n) -> _ -> _) eq_op.
Proof. param_comp eq_seqmx_R. Qed.

End seqmx_param.
End seqmx_theory.

Section testmx.

Require Import binint ssrint poly seqpoly.

Goal ((0 : 'M[int]_(2,2)) == 0).
rewrite [_ == _]refines_eq.
by compute.
(* erewrite refines_eq; last first. *)
(* eapply refines_bool_eq; tc. *)
(* eapply refines_apply; tc. *)
(* eapply refines_apply; tc. *)
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

Goal (M3 + Mn3 == 0).
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

End testmx.