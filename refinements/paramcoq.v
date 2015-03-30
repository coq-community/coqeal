Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly polydiv.
Require Import ssrint ZArith.

Require Import hrel param.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.

Delimit Scope computable_scope with C.
(* Delimit Scope rel_scope with rel. *)

(* Shortcut for triggering typeclass resolution *)
Ltac tc := do 1?typeclasses eauto.

Section refinements.

Local Open Scope rel.

Fact refines_key : unit. Proof. done. Qed.
Class refines A B (R : A -> B -> Type) (m : A) (n : B) :=
  refines_rel : (locked_with refines_key R) m n.

Lemma refinesE A B (R : A -> B -> Type) : refines R = R.
Proof. by rewrite /refines unlock. Qed.

Lemma refines_eq T (x y : T) : refines eq x y -> x = y.
Proof. by rewrite refinesE. Qed.

Global Instance refines_bool_eq x y : refines bool_R x y -> refines eq x y.
Proof. by rewrite !refinesE=> [[]]. Qed.

Lemma nat_R_eq x y : nat_R x y -> x = y.
Proof. by elim=> // m n _ ->. Qed.

(* Global Instance refines_nat_eq x y : refines nat_R x y -> refines eq x y. *)
(* Proof. rewrite !refinesE; exact: nat_R_eq. Qed. *)

Lemma refinesP T T' (R : T -> T' -> Type) (x : T) (y : T') :
  refines R x y -> R x y.
Proof. by rewrite refinesE. Qed.

Fact composable_lock : unit. Proof. exact tt. Qed.
Class composable {A B C}
 (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :=
  Composable : locked_with composable_lock (rAB \o rBC <= rAC).

Lemma composableE A B C
 (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type) :
  composable rAB rBC rAC = (rAB \o rBC <= rAC).
Proof. by rewrite /composable unlock. Qed.

Lemma refines_trans A B C
  (rAB : A -> B -> Type) (rBC : B -> C -> Type) (rAC : A -> C -> Type)
  (a : A) (b : B) (c : C) : composable rAB rBC rAC ->
  refines rAB a b -> refines rBC b c -> refines rAC a c.
Proof.
by rewrite !refinesE composableE => rABC rab rbc; apply: rABC; exists b.
Qed.

Lemma trivial_refines T T' (R : T -> T' -> Type) (x : T) (y : T') :
  R x y -> refines R x y.
Proof. by rewrite refinesE. Qed.

Global Instance refines_apply
   A B (R : A -> B -> Type) C D (R' : C -> D -> Type) :
   forall (c : A -> C) (d : B -> D), refines (R ==> R') c d ->
   forall (a : A) (b : B), refines R a b -> refines R' (c a) (d b).
Proof. by rewrite !refinesE => c d rcd a b rab; apply: rcd. Qed.

Global Instance composable_rid1 A B (R : A -> B -> Type) : composable eq R R | 1.
Proof. by rewrite composableE; apply: (eq_hrelRL (comp_eql _)). Qed.

Global Instance composable_bool_id1 B (R : bool -> B -> Type) : composable bool_R R R | 1.
Proof. by rewrite composableE => x y [y' [[]]]. Qed.

(* Global Instance composable_nat_id1 B (R : nat -> B -> Type) : composable nat_R R R | 1. *)
(* Proof. by rewrite composableE => x y [y' [/nat_R_eq ->]]. Qed. *)

Global Instance composable_comp A B C (rAB : A -> B -> Type)
  (rBC : B -> C -> Type) : composable rAB rBC (rAB \o rBC).
Proof. by rewrite composableE. Qed.

Global Instance composable_imply {A B C A' B' C'}
  (rAB : A -> B -> Type) (rBC : B -> C -> Type)
  (R1 : A' -> B' -> Type) (R2 : B' -> C' -> Type) (R3 : A' -> C' -> Type):
  composable R1 R2 R3 -> composable (rAB ==> R1) (rBC ==> R2) (rAB \o rBC ==> R3) | 0.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c [b [rABab rBCbc]].
apply: R123; exists (fB b); split; [ exact: RfAB | exact: RfBC ].
Qed.

Global Instance composable_imply_id1 {A B A' B' C'}
  (rAB : A -> B -> Type)
  (R1 : A' -> B' -> Type) (R2 : B' -> C' -> Type) (R3 : A' -> C' -> Type) :
  composable R1 R2 R3 -> composable (eq ==> R1) (rAB ==> R2) (rAB ==> R3) | 1.
Proof.
rewrite !composableE => R123 fA fC [fB [RfAB RfBC]] a c rABac.
apply: R123; exists (fB a); split; [ exact: RfAB | exact: RfBC ].
Qed.

(* Composable and pairs *)
Lemma prod_hrel_R A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) x y :
  prod_R rA rB x y -> prod_hrel rA rB x y.
Proof. by case; split. Qed.

Global Instance composable_prod A A' B B' C C'
  (rAB : A -> B -> Type) (rAB' : A' -> B' -> Type)
  (rBC : B -> C -> Type) (rBC' : B' -> C' -> Type)
  (rAC : A -> C -> Type) (rAC' : A' -> C' -> Type) :
    composable rAB rBC rAC ->
    composable rAB' rBC' rAC' ->
    composable (prod_hrel rAB rAB') (prod_R rBC rBC')
               (prod_R rAC rAC') | 1.
Proof.
rewrite !composableE=> h1 h2 [a a'] [c c'] [[b b']].
case=> [[/= rab rab']] /prod_hrel_R [/= rbc rbc'].
by split; [ apply: h1; exists b | apply: h2; exists b'].
Qed.

(* Global Instance refines_pair *)
(*   A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) : *)
(*   refines (rA ==> rB ==> prod_hrel rA rB)%rel (@pair _ _) (@pair _ _). *)
(* Proof. by rewrite refinesE. Qed. *)

(* Global Instance refines_fst *)
(*   A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) : *)
(*   refines (prod_hrel rA rB ==> rA)%rel (@fst _ _) (@fst _ _). *)
(* Proof. by rewrite !refinesE=> [??] [??]. Qed. *)

(* Global Instance refines_snd *)
(*   A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) : *)
(*   refines (prod_hrel rA rB ==> rB)%rel (@snd _ _) (@snd _ _). *)
(* Proof. by rewrite !refinesE=> [??] [??]. Qed. *)

End refinements.

Hint Extern 0 (refines _ _ _)
  => apply trivial_refines; eassumption : typeclass_instances.

(* Tactic for doing parametricity proofs, take parametricity theorem
   generated by the Parametricity plugin as argument *)
Ltac param x :=
  rewrite refinesE; do?move=> ?*;
  eapply x=> // *; eapply refinesP;
  do ?eapply refines_apply; tc.

(* Special tactic when relation is defined using \o *)
Ltac param_comp x := eapply refines_trans; tc; param x.

Module Op.

Class zero A := zero_op : A.
Local Notation "0" := zero_op : computable_scope.

Class one A := one_op : A.
Local Notation "1" := one_op : computable_scope.

Class opp A := opp_op : A -> A.
Local Notation "-%C" := opp_op.
Local Notation "- x" := (opp_op x) : computable_scope.

Class add A := add_op : A -> A -> A.
Local Notation "+%C" := add_op.
Local Notation "x + y" := (add_op x y) : computable_scope.

Class sub B := sub_op : B -> B -> B.
Local Notation "x - y" := (sub_op x y) : computable_scope.

Class mul B := mul_op : B -> B -> B.
Local Notation "*%C" := mul_op.
Local Notation "x * y" := (mul_op x y) : computable_scope.

Class scale A B := scale_op : A -> B -> B.
Local Notation "*:%C" := scale_op.
Local Notation "x *: y" := (scale_op x y) : computable_scope.

Class eq B := eq_op : B -> B -> bool.
Local Notation "x == y" := (eq_op x y) : computable_scope.

Class leq B := leq_op : B -> B -> bool.
Local Notation "x <= y" := (leq_op x y) : computable_scope.

Class spec_of A B   := spec : A -> B.
Class implem_of A B := implem : A -> B.

(* Classes for karatsuba *)
Class shift_of polyA := shift_op : nat -> polyA -> polyA.
Class size_of polyA := size_op : polyA -> nat.
Class split_of polyA := split_op : nat -> polyA -> polyA * polyA.

End Op.

Import Op.

Notation "0"       := zero_op        : computable_scope.
Notation "1"       := one_op         : computable_scope.
Notation "-%C"     := opp_op.
Notation "- x"     := (opp_op x)     : computable_scope.
Notation "+%C"     := add_op.
Notation "x + y"   := (add_op x y)   : computable_scope.
Notation "x - y"   := (sub_op x y)   : computable_scope.
Notation "*%C"     := mul_op.
Notation "x * y"   := (mul_op x y)   : computable_scope.
Notation "*:%C"    := scale_op.
Notation "x *: y"  := (scale_op x y)    : computable_scope.
Notation "x == y"  := (eq_op x y)    : computable_scope.
Notation "x <= y"  := (leq_op x y)   : computable_scope.

Ltac simpC :=
  do ?[ rewrite -[0%C]/0%R
      | rewrite -[1%C]/1%R
      | rewrite -[(_ + _)%C]/(_ + _)%R
      | rewrite -[(_ + _)%C]/(_ + _)%N
      | rewrite -[(- _)%C]/(- _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%N
      | rewrite -[(_ * _)%C]/(_ * _)%R
      | rewrite -[(_ * _)%C]/(_ * _)%N
      | rewrite -[(_ == _)%C]/(_ == _)%bool
      ].

(* Bin nat refines ssr nat *)
Section binnat_op.

Global Instance zero_N : zero N := N.zero.
Global Instance one_N  : one N  := N.one.
Global Instance add_N  : add N  := N.add.
Global Instance eq_N   : eq N  := N.eqb.
Global Instance spec_N : spec_of N nat := nat_of_bin.
Global Instance implem_N : implem_of nat N := bin_of_nat.

End binnat_op.

Section binnat_theory.

Local Open Scope rel_scope.

Definition Rnat : nat -> N -> Type := fun n n' => n = nat_of_bin n'.

Global Instance Rnat_0 : refines Rnat 0%nat 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_1 : refines Rnat 1%nat 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rnat_add :
  refines (Rnat ==> Rnat ==> Rnat) (fun m n => m + n)%nat +%C.
Proof. by rewrite !refinesE=> m m' -> n n' ->; rewrite -nat_of_add_bin. Qed.

Global Instance Rnat_eq : refines (Rnat ==> Rnat ==> bool_R) eqtype.eq_op eq_op.
Proof.
rewrite !refinesE=> m m' -> n n' ->; rewrite /eq_op /eq_N.
case: (N.eqb_spec _ _) => [->|/eqP hneq].
  by rewrite eqxx; exact: true_R.
suff H : (nat_of_bin m' == nat_of_bin n') = false.
  by rewrite H; exact: false_R.
by apply/negP => [/eqP /(can_inj nat_of_binK)]; apply/eqP.
Qed.

End binnat_theory.

Section testnat.

Local Instance Rnat_implem n : refines Rnat n (implem n) | 999.
Proof. by rewrite refinesE /Rnat /implem /implem_N bin_of_natK. Qed.

Goal (1 == 1)%nat.
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (100 == 100)%nat.
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (998 + 2 == 1000)%nat.
rewrite [_ == _]refines_eq.
by compute.
Abort.

End testnat.

Section binint_op.

Definition int_of_Z (n : Z) : int := match n with
  | Z0 => Posz 0
  | Zpos p => Posz (nat_of_pos p)
  | Zneg p => Negz (nat_of_pos p).-1
  end.

Definition Z_of_int (n : int) : Z := match n with
  | Posz n => Z.of_nat n
  | Negz n => - (Z.of_nat n.+1)
  end.

Global Instance zero_Z : zero Z := Z.zero.
Global Instance one_Z  : one Z  := Z.one.
Global Instance add_Z  : add Z  := Z.add.
Global Instance mul_Z  : mul Z  := Z.mul.
Global Instance opp_Z  : opp Z  := Z.opp.
Global Instance eq_Z   : eq Z   := Z.eqb.

Global Instance spec_Z : spec_of Z int := int_of_Z.
Global Instance implem_Z : implem_of int Z := Z_of_int.

End binint_op.

Section binint_theory.

Local Open Scope rel_scope.

Definition Rint : int -> Z -> Type := fun n n' => n = int_of_Z n'.

Global Instance Rint_0 : refines Rint 0 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rint_1 : refines Rint 1 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rint_opp : refines (Rint ==> Rint) -%R -%C.
Admitted.

Global Instance Rint_add : refines (Rint ==> Rint ==> Rint) +%R +%C.
Admitted.

Global Instance Rint_mul : refines (Rint ==> Rint ==> Rint) *%R *%C.
Admitted.

Global Instance Rint_eq : refines (Rint ==> Rint ==> bool_R) eqtype.eq_op eq_op.
Admitted.

Global Instance Rint_implem n : refines Rint n (implem n) | 999.
Admitted.

End binint_theory.

Section testint.

Goal (1 == 1 :> int).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (10%:Z - 5%:Z == 1 + 4%:Z).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (1000%:Z == 998%:Z + 2%:Z).
rewrite [_ == _]refines_eq.
by compute.
Abort.

End testint.

Section seqpoly_op.

Local Open Scope computable_scope.

Variable T : Type.

Definition seqpoly := seq T.

Context `{zero T, one T, add T, opp T, mul T, eq T}.

Global Instance seqpoly0 : zero seqpoly := [::].
Global Instance seqpoly1 : one seqpoly := [:: 1].
Global Instance seqpoly_opp : opp seqpoly := List.map -%C.

Fixpoint add_seqpoly (p q : seqpoly) : seqpoly := match p,q with
  | [::], q => q
  | p, [::] => p
  | a :: p', b :: q' => a + b :: add_seqpoly p' q'
  end.

Global Instance seqpoly_add : add seqpoly := add_seqpoly.
Global Instance seqpoly_sub : sub seqpoly := fun x y => (x + - y)%C.

Global Instance seqpoly_scale : scale T seqpoly := fun a => map ( *%C a).

Global Instance shift : shift_of seqpoly := fun n => ncons n 0%C.
Arguments shift n p : simpl nomatch.

Global Instance seqpoly_mul : mul seqpoly := fun p q =>
  let fix aux p :=
      if p is a :: p then (a *: q + shift 1%nat (aux p))%C else 0
  in aux p.

Global Instance size_seqpoly : size_of seqpoly :=
  let fix aux p :=
      if p is a :: p then
        let sp := aux p in
        if (eqn sp 0)%nat then ~~ (a == 0)%C : nat else sp.+1
      else 0%nat in aux.

Global Instance seqpoly_eq : eq seqpoly := fun p q =>
  all (fun x => x == 0)%C (p - q)%C.

Global Instance split_seqpoly : split_of seqpoly := fun n p => 
  (take n p,drop n p).

End seqpoly_op.

Parametricity seqpoly0.
Parametricity seqpoly1.
Parametricity seqpoly_opp.
Parametricity seqpoly_add.
Parametricity seqpoly_sub.
Parametricity seqpoly_scale.
Parametricity shift.
Parametricity seqpoly_mul.
Parametricity size_seqpoly.
Parametricity seqpoly_eq.
Parametricity split_seqpoly.

Section seqpoly_theory.

Variable R : ringType.

Local Instance zeroR : zero R := 0%R.
Local Instance oneR  : one R  := 1%R.
Local Instance addR  : add R  := +%R.
Local Instance mulR  : mul R  := *%R.
Local Instance oppR  : opp R  := -%R.
Local Instance eqR   : eq R   := eqtype.eq_op.

Definition splitp : nat -> {poly R} -> {poly R} * {poly R} :=
  fun n p => (rdivp p 'X^n, rmodp p 'X^n).

Lemma seqpoly_of_polyK : pcancel (@polyseq R) (some \o Poly).
Proof. by move=> p /=; rewrite polyseqK. Qed.

Definition Rseqpoly : {poly R} -> seqpoly R -> Type := fun p sp => p = Poly sp.

Local Open Scope rel_scope.

Instance Rseqpoly_cons : refines (Logic.eq ==> Rseqpoly ==> Rseqpoly) (@cons_poly R) cons.
Proof.
rewrite !refinesE => x y -> p sp hp.
apply/polyP => i /=.
rewrite cons_poly_def.
admit.
Qed.

Instance Rseqpoly_0 : refines Rseqpoly 0%R 0%C.
Proof. by rewrite refinesE. Qed.

Instance Rseqpoly_1 : refines Rseqpoly 1%R 1%C.
Proof. by rewrite refinesE /Rseqpoly /= cons_poly_def mul0r add0r. Qed.

Instance Rseqpoly_opp : refines (Rseqpoly ==> Rseqpoly) -%R -%C.
Proof.
rewrite refinesE /Rseqpoly => p sp -> {p}.
apply/polyP => i /=; rewrite /opp_op /seqpoly_opp /=.
rewrite coef_opp_poly !coef_Poly.
have [hlt|hleq] := ltnP i (size sp); first by rewrite (nth_map 0%C).
by rewrite !nth_default ?oppr0 ?size_mkseq ?size_map.
Qed.

Instance Rseqpoly_add : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) +%R +%C.
Proof.
rewrite refinesE /Rseqpoly => p sp -> q sq -> {p q}.
elim: sp sq=> [[] /= *|a p ih [|b q]] /=; do ?rewrite ?add0r ?addr0 //.
by rewrite !cons_poly_def -ih addrAC addrA -mulrDl raddfD /= -!addrA [_ + a%:P]addrC.
Qed.

Instance Rseqpoly_sub : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) (fun x y => x - y) sub_op.
Admitted.

(* scaling *)
Instance Rseqpoly_scale : refines (Logic.eq ==> Rseqpoly ==> Rseqpoly) *:%R *:%C.
Admitted.

(* This needs to be added to be able to use the instance below *)
Definition shiftp n (p : {poly R}) := p * 'X^n.

(* These can be done with Logic.eq instead of nat_R *)
Instance Rseqpoly_shift :
  refines (Logic.eq ==> Rseqpoly ==> Rseqpoly) shiftp shift_op.
Admitted.

Instance Rseqpoly_split :
  refines (Logic.eq ==> Rseqpoly ==> prod_hrel Rseqpoly Rseqpoly) splitp split_op.
Admitted.

(* multiplication *)
Instance Rseqpoly_mul : refines (Rseqpoly ==> Rseqpoly ==> Rseqpoly) *%R *%C.
Admitted.

(* This definition hides the coercion which makes it possible for proof search
   to find Rseqpoly_seqpoly_size *)
Definition sizep : {poly R} -> nat := size.
Lemma sizepE s : sizep s = size s. Proof. by []. Qed.

Instance Rseqpoly_size :
  refines (Rseqpoly ==> Logic.eq) sizep size_op.
Admitted.

Instance Rseqpoly_eq : refines (Rseqpoly ==> Rseqpoly ==> bool_R) eqtype.eq_op eq_op.
Admitted.

Section seqpoly_param.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero C, one C, opp C, add C, mul C, eq C}.
Context `{implem_of R C}.
Context `{!refines rAC 0%R 0%C, !refines rAC 1%R 1%C}.
Context `{!refines (rAC ==> rAC) -%R -%C}.
Context `{!refines (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!refines (rAC ==> rAC ==> bool_R) eqtype.eq_op eq_op}.

Definition RseqpolyC : {poly R} -> seq C -> Type :=
  (Rseqpoly \o (list_R rAC)).

Global Instance RseqpolyC_cons :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) (@cons_poly R) cons.
Proof. param_comp cons_R. Qed.

Global Instance RseqpolyC_0 : refines RseqpolyC 0%R 0%C.
Proof. param_comp seqpoly0_R. Qed.

Global Instance RseqpolyC_1 : refines RseqpolyC 1%R 1%C.
Proof. param_comp seqpoly1_R. Qed.

Global Instance RseqpolyC_opp : refines (RseqpolyC ==> RseqpolyC) -%R -%C.
Proof. param_comp seqpoly_opp_R. Qed.

Global Instance RseqpolyC_add : 
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) +%R +%C.
Proof. param_comp seqpoly_add_R. Qed.

Global Instance RseqpolyC_sub : 
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) (fun x y => x - y) sub_op.
Proof. param_comp seqpoly_sub_R. Qed.

Global Instance RseqpolyC_scale :
  refines (rAC ==> RseqpolyC ==> RseqpolyC) *:%R *:%C.
Proof. param_comp seqpoly_scale_R. Qed.

(* This should use nat_R and not Logic.eq *)
Global Instance RseqpolyC_shift :
  refines (nat_R ==> RseqpolyC ==> RseqpolyC) shiftp shift_op.
Proof. param_comp shift_R. Qed.

(* Uses composable_prod *)
Global Instance RseqpolyC_split :
  refines (nat_R ==> RseqpolyC ==> prod_R RseqpolyC RseqpolyC)
    splitp split_op.
Proof. param_comp split_seqpoly_R. Qed.

(* Lower priority to make karatsuba default instance *)
Global Instance RseqpolyC_mul :
  refines (RseqpolyC ==> RseqpolyC ==> RseqpolyC) *%R *%C | 1.
Proof. param_comp seqpoly_mul_R. Qed.

Global Instance RseqpolyC_size :
  refines (RseqpolyC ==> nat_R) sizep size_op.
Proof. param_comp size_seqpoly_R. Qed.

Global Instance RseqpolyC_eq :
  refines (RseqpolyC ==> RseqpolyC ==> bool_R) eqtype.eq_op eq_op.
Proof. param_comp seqpoly_eq_R. Qed.

End seqpoly_param.
End seqpoly_theory.

Section testpoly.

Goal (1 == (1 : {poly {poly {poly int}}})).
rewrite [_ == _]refines_eq.
do ?rewrite /one_op /seqpoly1.
by compute.
Abort.
 
Goal (Poly [:: 1; 2%:Z; 3%:Z] + Poly [:: 1; 2%:Z; 3%:Z]) == Poly [:: 1 + 1; 2%:Z + 2%:Z; 2%:Z + 4%:Z].
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Goal (- 1 == - (1: {poly {poly int}})).
rewrite [_ == _]refines_eq.
by compute.
Abort.

Goal (- Poly [:: 1; 2%:Z; 3%:Z]) == Poly [:: - 1; - 2%:Z; - 3%:Z].
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z; 3%:Z] - Poly [:: 1; 2%:Z; 3%:Z]) == 0.
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Goal (Poly [:: 1; 2%:Z] * Poly [:: 1; 2%:Z]) == Poly [:: 1; 4%:Z; 4%:Z].
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999. 
Proof. by rewrite refinesE; elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed.

Goal (2%:Z *: shiftp 2%nat 1 == Poly [:: 0; 0; 2%:Z]).
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

(* sizep gives a nat, should one handle it like this? *)
Local Instance refines_eq_nat  :
  refines (nat_R ==> nat_R ==> bool_R)%rel eqtype.eq_op eqn.
Proof.
rewrite refinesE /eqtype.eq_op /= => m n /nat_R_eq -> m' n' /nat_R_eq ->.
case: (eqn _ _); [ exact: true_R | exact: false_R ].
Qed.

Goal (sizep (Poly [:: 1; 2%:Z; 3%:Z]) == 3%nat).
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

(* This is not working... *)
(* Goal (split_polyR 2%nat (Poly [:: 1; 2%:Z; 3%:Z; 4%:Z]) == *)
(*      (Poly [:: 1; 2%:Z],Poly [:: 3%:Z; 4%:Z])). *)
(* rewrite /= [_ == _]refines_eq. *)
(* by compute. *)
(* Abort. *)

End testpoly.

Section generic_karatsuba.

Variable polyA : Type.

Context `{add polyA, mul polyA, sub polyA}.
Context `{shift_poly : shift_of polyA, size_poly : size_of polyA}.
Context `{split_poly : split_of polyA}.

Fixpoint karatsuba_rec n (p q : polyA) := match n with
  | 0     => (p * q)%C
  | n'.+1 => 
      let sp := size_poly p in let sq := size_poly q in 
      if (sp <= 2) || (sq <= 2) then (p * q)%C else
        let m       := minn sp./2 sq./2 in
        let (p1,p2) := split_poly m p in
        let (q1,q2) := split_poly m q in
        let p1q1    := karatsuba_rec n' p1 q1 in
        let p2q2    := karatsuba_rec n' p2 q2 in
        let p12     := (p1 + p2)%C in
        let q12     := (q1 + q2)%C in
        let p12q12  := karatsuba_rec n' p12 q12 in
        (shift_poly (2 * m)%nat p1q1 +
         shift_poly m (p12q12 - p1q1 - p2q2) +
         p2q2)%C
  end.

Definition karatsuba p q :=
  karatsuba_rec (maxn (size_poly p) (size_poly q)) p q.

End generic_karatsuba.

Parametricity karatsuba.
Parametricity karatsuba_rec.

Section karatsuba_theory.

Local Open Scope rel_scope.

Variable R : ringType.

Instance add_polyR : add {poly R} := +%R.
Instance mul_polyR : mul {poly R} := *%R.
Instance sub_polyR : sub {poly R} := fun x y => (x - y)%R.
Instance shift_polyR : shift_of {poly R} := shiftp (R:=R).
Instance size_polyR : size_of {poly R} := sizep (R:=R).
Instance split_polyR : split_of {poly R} := splitp (R:=R).

Lemma karatsuba_recE n (p q : {poly R}) : karatsuba_rec n p q = p * q.
Proof.
elim: n=> //= n ih in p q *; case: ifP=> // _; set m := minn _ _.
rewrite [p in RHS](rdivp_eq (monicXn _ m)) [q in RHS](rdivp_eq (monicXn _ m)).
rewrite /shift_op /shift_polyR /shiftp.
rewrite !ih !(mulrDl, mulrDr, mulNr) mulnC exprM.
rewrite -addrA -opprD [X in X + _ - _]addrC addrACA addrK.
by simpC; rewrite !(commr_polyXn, mulrA, addrA).
Qed.

Lemma karatsubaE (p q : {poly R}) : karatsuba p q = p * q.
Proof. exact: karatsuba_recE. Qed.

Section karatsuba_param.

Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).
Context `{add polyC, mul polyC, sub polyC}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) +%R +%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) *%R *%C}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) (fun x y => x - y)%R sub_op}.

Context `{!shift_of polyC}.
Context `{!refines (nat_R ==> RpolyC ==> RpolyC) shift_polyR shift_op}.

Context `{!size_of polyC}.
Context `{!refines (RpolyC ==> nat_R) size_polyR size_op}.

Context `{!split_of polyC}.
Context `{!refines (nat_R ==> RpolyC ==> prod_R RpolyC RpolyC) split_polyR split_op}.

Global Instance RpolyC_karatsuba_rec :
  refines (nat_R ==> RpolyC ==> RpolyC ==> RpolyC)
    (karatsuba_rec (polyA:={poly R})) (karatsuba_rec (polyA:=polyC)).
Proof. param karatsuba_rec_R. Qed.

Global Instance RpolyC_karatsuba :
  refines (RpolyC ==> RpolyC ==> RpolyC)
    (karatsuba (polyA:={poly R})) (karatsuba (polyA:=polyC)).
Proof. param karatsuba_R. Qed.

(* Give this higher priority than the instance for mul_seqpoly so that it
   gets found instead *)
Global Instance RpolyC_karatsuba_mul :
  refines (RpolyC ==> RpolyC ==> RpolyC) *%R (karatsuba (polyA:=polyC)) | 0.
Proof.
by rewrite refinesE; do?move=> ?*; rewrite -karatsubaE; apply: refinesP; tc.
Qed.

End karatsuba_param.
End karatsuba_theory.

Section test_karatsuba.

Goal (Poly [:: 1; 2%:Z] * Poly [:: 1; 2%:Z]) == Poly [:: 1; 4%:Z; 4%:Z].
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

Fixpoint bigseq (x : int) (n : nat) : seq int := match n with
  | 0 => [:: x]
  | n'.+1 => x :: bigseq (x+1) n'
  end.

Let p1 := Eval compute in bigseq 1 10.
Let p2 := Eval compute in bigseq 2 10.

(* TODO: Translate Poly directly? *)
Goal (Poly p1 * Poly p2 == Poly p2 * Poly p1).
rewrite /= [_ == _]refines_eq.
by compute.
Abort.

End test_karatsuba.

Section testmx.
Variable mxA : nat -> nat -> Type.
Definition idmx (m n : nat) (mx : mxA m n) : mxA m n := mx.
End testmx.
Parametricity idmx.
Print idmx_R. (* Here we get something too general! *)

