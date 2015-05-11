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

(* Section classes. *)

(* Class hzero_of {I} B := hzero_op : forall {m n : I}, B m n. *)

(* End classes. *)

(* Notation "0" := hzero_op : hetero_computable_scope. *)

Section seqmx_op.

Variable A : Type.

Definition seqmx := seq (seq A).

Context `{zero_of A, one_of A, add_of A, opp_of A, eq_of A}.

Definition const_seqmx m n (x : A) := nseq m (nseq n x).
Definition map_seqmx (f : A -> A) (M : seqmx) := map (map f) M. 

Global Instance seqmx0 m n : zero_of seqmx := const_seqmx m n 0%C.
(* Global Instance seqpoly1 : one_of seqpoly := [:: 1]. *)
Global Instance seqmx_opp : opp_of seqmx := map_seqmx -%C.

(* Inlining of && should provide lazyness here. *)
Fixpoint eq_seq T f (s1 s2 : seq T) :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => f x1 x2 && eq_seq f s1' s2'
  | _, _ => false
  end.

Global Instance eq_seqmx : eq_of seqmx := eq_seq (eq_seq eq_op).

(* Definition ord_enum_eq n : seq 'I_n := pmap (insub_eq _) (iota 0 n). *)

(* Definition mkseqmx m n (f : nat -> nat -> A) : seqmx := *)
(*   [seq [seq f i j | j <- iota 0 n] | i <- iota 0 m]. *)

(* Definition mkseqmx_ord m n (f : 'I_m -> 'I_n -> A) : seqmx := *)
(*   let enum_n := ord_enum_eq n in *)
(*   map (fun i => map (f i) enum_n) (ord_enum_eq m). *)

End seqmx_op.

Parametricity const_seqmx.
Parametricity map_seqmx.
Parametricity seqmx0.
Parametricity seqmx_opp.
Parametricity eq_seq.
Parametricity eq_seqmx.

(* Parametricity Inductive ordinal. *)
(* Parametricity Inductive subType. *)
(* Parametricity ord_enum_eq. *)
(* Parametricity mkseqmx. *)
(* Parametricity mkseqmx_ord. *)

Section seqmx_theory.

Variable R : ringType.

Local Instance zeroR : zero_of R := 0%R.
Local Instance oppR  : opp_of R := -%R.
Local Instance eqR   : eq_of R   := eqtype.eq_op.

CoInductive Rseqmx {m n} : 'M[R]_(m,n) -> seqmx R -> Type :=
  Rseqmx_spec (A : 'M[R]_(m,n)) M of
    size M = m
  & forall i, i < m -> size (nth [::] M i) = n
  & (forall i j, (A i j = nth 0 (nth [::] M i) j)) : Rseqmx A M.

(* Used to refine a Matrix (maybe do it directly for the notation?) *)
Check Matrix.
Check cons_poly.

(* Definition seqmx_of_mx m n (M : 'M[R]_(m,n)) : seqmx R := *)
(*   [seq [seq M i j | j <- enum 'I_n] | i <- enum 'I_m]. *)

(* Instance Rseqmx_Matrix : refines (Logic.eq ==> Rseqmx ==> Rseqpoly) (@cons_poly R) cons. *)

(* Global Instance Rseqmx_implem m n (M : 'M[R]_(m,n)) : *)
(*   refines Rseqmx n (implem n) | 999. *)

(* Instance Rseqmx_mkseqmx_ord : refines (Logic.eq ==> Rseqpoly ==> Rseqpoly) (@cons_poly R) cons. *)

(* Instance Rseqmx_mkseqmx_ord_mx_key m n : *)
(*   refines ((Logic.eq ==> Logic.eq ==> Logic.eq) ==> Rseqmx) *)
(*         (matrix_of_fun matrix_key) (@mkseqmx_ord R m n). *)
(* Proof. admit. Qed. *)

Instance Rseqmx_0 m n : refines Rseqmx (0 : 'M[R]_(m,n)) (seqmx0 m n).
Proof.
rewrite refinesE; constructor=>[|i|i j]; first by rewrite size_nseq.
  by rewrite nth_nseq => ->; rewrite size_nseq.
by rewrite mxE !(nth_nseq,ltn_ord).
Qed.

Instance Rseqmx_opp m n : refines (Rseqmx ==> Rseqmx) (-%R : 'M[R]_(m,n) -> 'M[R]_(m,n)) (@seqmx_opp R oppR).
Proof.
rewrite refinesE=> ? ? [A M h1 h2 h3].
constructor; first by rewrite size_map h1.
  move=> i him.
  rewrite (nth_map [::]); last by rewrite h1.
  by rewrite size_map h2.
move=> i j.
rewrite mxE.
rewrite /seqmx_opp.
rewrite (nth_map [::]); last by rewrite h1 ltn_ord.
rewrite (nth_map 0); first by rewrite h3.
by rewrite h2 !ltn_ord.
Qed.

Instance Rseqmx_eq m n :
  refines (Rseqmx ==> Rseqmx ==> bool_R) (eqtype.eq_op : 'M[R]_(m,n) -> _ -> _) eq_op.
Proof. admit. Qed.

Section seqmx_param.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, eq_of C}.
Context `{!refines rAC 0%R 0%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.

Definition RseqmxC {m n} := (@Rseqmx m n \o (list_R (list_R rAC)))%rel.

(* Global Instance RseqmxA_mkseqmx_ord_mx_key m n : *)
(*   refines ((Logic.eq ==> Logic.eq ==> rAC) ==> RseqmxC) *)
(*         (matrix_of_fun matrix_key) (@mkseqmx_ord C m n). *)
(* Proof. *)

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999. 
Proof. by rewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed.

Global Instance RseqmxC_0 m n : refines RseqmxC (0 : 'M[R]_(m,n)) (seqmx0 m n).
Proof.
eapply refines_trans; tc.
eapply Rseqmx_0.
param seqmx0_R.
Qed.

Global Instance RseqmxC_eq m n :
  refines (RseqmxC ==> RseqmxC ==> bool_R) (eqtype.eq_op : 'M[R]_(m,n) -> _ -> _) eq_op.
Proof. param_comp eq_seqmx_R. Qed.

End seqmx_param.
End seqmx_theory.

Section testmx.

Require Import binint ssrint.

(* This is not found by rewrite [_ == _]refines_eq... *)
Goal ((0 : 'M[int]_(2,2)) == 0).
erewrite refines_eq; last first.
eapply refines_bool_eq; tc.
eapply refines_apply; tc.
eapply refines_apply; tc.
eapply RseqmxC_0; tc.
eapply RseqmxC_0; tc.
by compute.
Abort.

End testmx.