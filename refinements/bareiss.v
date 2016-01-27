(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
(* Formalization of the Sasaki-Murao algorithm *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path ssralg.
From mathcomp Require Import fintype perm choice matrix bigop zmodp poly polydiv mxpoly.

From CoqEAL Require Import hrel param refinements minor seqmx seqpoly.

Import Refinements.Op.
Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Local Open Scope ring_scope.

Section generic_bareiss.
(* Variable ord : nat -> Type. *)
(* Context `{fun_of polyR ord mxpolyR, forall n, zero (ord (1 + n))}. *)

Local Open Scope computable_scope.

Variable R : Type.
Variable polyR : Type.
(* Variable mxR : nat -> nat -> Type. *)
Variable mxpolyR : nat -> nat -> Type.

Context `{zero_of R}.
Context `{one_of polyR}.
(* Context `{forall m n, opp_of (mxR m n)}. *)
Context `{ursubmx : ursubmx_of mxpolyR}.
Context `{dlsubmx : dlsubmx_of mxpolyR}.
Context `{drsubmx : drsubmx_of mxpolyR}.
Context `{!hmul_of mxpolyR}.
(* Context `{forall m n, opp_of (mxpolyR m n)}. *)
Context `{forall m n, sub_of (mxpolyR m n)}.
Context `{forall m n, scale_of polyR (mxpolyR m n)}.
Context `{map_mx : forall m n, map_mx_of polyR (mxpolyR m n)}.
Context `{top_left : forall m, top_left_of (mxpolyR (1 + m) (1 + m)) polyR}.
Context `{divp : div_of polyR}.
Context `{head : lead_coef_of R polyR}.

(* Variable char_poly_mx : forall n, mxR n n -> mxpolyR n n. *)

Fixpoint bareiss_rec m (a : polyR) : mxpolyR (1 + m) (1 + m) -> polyR :=
  match m with
    | S p => fun (M : mxpolyR (1 + (1 + p)) (1 + (1 + p))) =>
      let d   := top_left M in
      let l   := ursubmx M in
      let c   := dlsubmx M in
      let N   := drsubmx M in
      let M'  := (d *: N - c *m l)%HC in
      let M'' := map_mx (fun x => x %/ a) M' in
        bareiss_rec d M''
    | _ => fun M => top_left M
  end.

Definition bareiss n (M : mxpolyR (1 + n) (1 + n)) := bareiss_rec 1 M.

(* Definition bareiss_char_poly n (M : mxR (1 + n) (1 + n)) := bareiss (char_poly_mx M). *)

(* The actual determinant function based on Bareiss *)
(* Definition bdet n (M : mxR (1 + n) (1 + n)) := head (bareiss_char_poly (- M)%HC). *)

End generic_bareiss.

Parametricity bareiss_rec.
Parametricity bareiss.

Print bareiss_R.

(* First some general lemmas *)
Section prelude.

Variable R : comRingType.

Lemma key_lemma m d l (c : 'cV[R]_m) M :
  d ^+ m * \det (block_mx d%:M l c M) = d * \det (d *: M - c *m l).
Proof.
rewrite -[d ^+ m]mul1r -det_scalar -(det1 _ 1) -(det_ublock _ 0) -det_mulmx.
rewrite mulmx_block ?(mul0mx,addr0,add0r,mul1mx,mul_scalar_mx) -2![LHS]mul1r.
rewrite -{1}(@det1 _ 1) -{2}(@det1 _ m) mulrA -(@det_lblock _ _ _ _ (- c)).
rewrite -det_mulmx mulmx_block ?(mul1mx,mul0mx,addr0) addrC mul_mx_scalar.
by rewrite scalerN subrr det_ublock det_scalar1 addrC mulNmx.
Qed.

(* The key lemma of our proof: after simplification, all the k-minors (involving *)
(* 1st line/column) can be divided by (M 0 0)^k *)
Lemma key_lemma_sub m n k (M : 'M[R]_(1 + m,1 + n))
  (f : 'I_k -> 'I_m) (g : 'I_k -> 'I_n) :
  M 0 0 * (minor f g (M 0 0 *: drsubmx M - dlsubmx M *m ursubmx M)) =
  M 0 0 ^+ k * (minor (lift_pred f) (lift_pred g) M).
Proof.
rewrite /minor -{7}[M]submxK submatrix_add submatrix_scale submatrix_opp.
have -> : ulsubmx M = (M 0 0)%:M by apply/rowP=> i; rewrite ord1 !mxE !lshift0.
by rewrite submatrix_lift_block key_lemma submatrix_mul.
Qed.

(* Why is this not in the libraries? *)
Lemma monic_lreg (p : {poly R}) : p \is monic -> GRing.lreg p.
Proof.
by rewrite monicE=> /eqP h; apply/lreg_lead; rewrite h; apply/lreg1.
Qed.

End prelude.

Section bareiss_correctness.

Variable R : comRingType.

(* Instance : fun_of {poly R} ordinal (matrix {poly R}) := @matrix.fun_of_matrix {poly R}. *)
(* Instance : forall n, zero 'I_(1 + n) := fun n => 0%R. *)

Instance : zero_of R := 0.
Instance : one_of {poly R} := 1.
Instance : div_of {poly R} := @rdivp R.
(* Instance : forall m n, opp_of (matrix R m n) := @oppmx R. *)
Instance : ursubmx_of (matrix {poly R}) := @matrix.ursubmx {poly R}.
Instance : dlsubmx_of (matrix {poly R}) := @matrix.dlsubmx {poly R}.
Instance : drsubmx_of (matrix {poly R}) := @matrix.drsubmx {poly R}.
Instance : hmul_of (matrix {poly R}) := @mulmx [ringType of {poly R}].
Instance : forall m n, sub_of (matrix {poly R} m n) :=
  fun m n (M N : 'M[{poly R}]_(m,n)) => M - N.
Instance : forall m n, scale_of {poly R} (matrix {poly R} m n) :=
  @scalemx [ringType of {poly R}].
Instance : forall m n, map_mx_of {poly R} (matrix {poly R} m n) :=
  fun m n f => @matrix.map_mx {poly R} {poly R} f m n.
Instance : forall m, top_left_of 'M[{poly R}]_(1 + m,1 + m) {poly R} :=
  fun m M => M ord0 ord0.

Lemma bareiss_recE : forall m a (M : 'M[{poly R}]_(1 + m)),
  a \is monic ->
 (forall p (h h' : p < 1 + m), pminor h h' M \is monic) ->
 (forall k (f g : 'I_k.+1 -> 'I_m.+1), rdvdp (a ^+ k) (minor f g M)) ->
  a ^+ m * (bareiss_rec a M) = \det M.
Proof.
elim=> [a M _ _ _|m ih a M am hpm hdvd] /=.
  by rewrite expr0 mul1r {2}[M]mx11_scalar det_scalar1.
have ak_monic k : a ^+ k \is monic by apply/monic_exp.
simpC.

(* TODO: Fix this: *)
rewrite /map_mx_of_instance_0 /drsubmx_of_instance_0 /dlsubmx_of_instance_0 /ursubmx_of_instance_0 /top_left_of_instance_0.

set d := M 0 0; set M' := (_ - _); set M'' := matrix.map_mx _ _; simpl in M'.
have d_monic : d \is monic.
  have -> // : d = pminor (ltn0Sn _) (ltn0Sn _) M.
  have h : widen_ord (ltn0Sn m.+1) =1 (fun _ => 0)
    by move=> x; apply/ord_inj; rewrite [x]ord1.
  by rewrite /pminor (minor_eq h h) minor1.
have dk_monic : forall k, d ^+ k \is monic by move=> k; apply/monic_exp.
have hM' : M' = a *: M''.
  pose f := fun m (i : 'I_m) (x : 'I_2) => if x == 0 then 0 else (lift 0 i).
  apply/matrixP => i j.
  rewrite !mxE big_ord1 !rshift1 [a * _]mulrC rdivpK ?(eqP am,expr1n,mulr1) //.
  move: (hdvd 1%nat (f _ i) (f _ j)).
  by rewrite !minor2 /f /= expr1 !mxE !lshift0 !rshift1.
rewrite -[M]submxK; apply/(@lregX _ d m.+1 (monic_lreg d_monic)).
have -> : matrix.ulsubmx M = d%:M by apply/rowP=> i; rewrite !mxE ord1 lshift0.
rewrite key_lemma -/M' hM' detZ mulrCA [_ * (a ^+ _ * _)]mulrCA !exprS -!mulrA.
rewrite ih // => [p h h'|k f g].
  rewrite -(@monicMl _ (a ^+ p.+1)) // -detZ -submatrix_scale -hM'.
  rewrite -(monicMl _ d_monic) key_lemma_sub monicMr //.
  by rewrite (minor_eq (lift_pred_widen_ord h) (lift_pred_widen_ord h')) hpm.
case/rdvdpP: (hdvd _ (lift_pred f) (lift_pred g)) => // x hx.
apply/rdvdpP => //; exists x.
apply/(@lregX _ _ k.+1 (monic_lreg am))/(monic_lreg d_monic).
rewrite -detZ -submatrix_scale -hM' key_lemma_sub mulrA [x * _]mulrC mulrACA.
by rewrite -exprS [_ * x]mulrC -hx.
Qed.

Lemma bareissE n (M : 'M[{poly R}]_(1 + n))
  (H : forall p (h h' : p < 1 + n), pminor h h' M \is monic) :
  bareiss M = \det M.
Proof.
rewrite /bareiss -(@bareiss_recE n 1 M) ?monic1 ?expr1n ?mul1r //.
by move=> k f g; rewrite expr1n rdvd1p.
Qed.

(* Lemma bareiss_char_polyE n (M : 'M[R]_(1 + n)) : *)
(*   bareiss_char_poly top_leftM (@rdivp R) (@char_poly_mx R) M = char_poly M. *)
(* Proof. *)
(* rewrite /bareiss_char_poly bareissE // => p h h'. *)
(* exact: pminor_char_poly_mx_monic. *)
(* Qed. *)

(* Lemma bdetE n (M : 'M[R]_(1 + n)) : bdet top_leftM (@rdivp R) (@char_poly_mx R) (fun s => s`_0) M = \det M. *)
(* Proof. *)
(* rewrite /bdet bareiss_char_polyE char_poly_det. *)
(* have -> : (-M)%HC = -M by []. *)
(* by rewrite -scaleN1r detZ mulrA -expr2 sqrr_sign mul1r. *)
(* Qed. *)

Section bareiss_param.

Local Open Scope rel_scope.

(* Instance : fun_of {poly R} ordinal (matrix {poly R}) := @matrix.fun_of_matrix {poly R}. *)
(* Instance : forall n, zero 'I_(1 + n) := fun n => 0%R. *)
(* Context `{fun_of polyR ordA mxpolyR}. *)
(* Context `{forall m, zero (ordA (1 + m))}. *)

Context (C : Type) (rRC : R -> C -> Type).
Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).

Definition mx : Type := nat -> nat -> Type.
Parametricity mx.
Print prod_R.
Print mx_R.

Context (mxpolyC : nat -> nat -> Type)


(** FOR PARAM WE SHOULD USE THIS RELATION!!! *)

        (* (RmxpolyC : forall m1 m2, nat_R m1 m2 -> *)
        (*             forall n1 n2, nat_R n1 n2 -> *)
        (*             'M[{poly R}]_(m1,n1) -> mxpolyC m2 n2 -> Type). *)
        (RmxpolyC : forall {m n}, 'M[{poly R}]_(m,n) -> mxpolyC m n -> Type).
(* Arguments RmxpolyC {_ _ _ _ _ _} _ _. *)
Arguments RmxpolyC {_ _} _ _.

Context `{zero_of C}.
(* Context `{!refines rRC 0%R 0%C}. *)

Context `{one_of polyC}.
(* Context `{!refines RpolyC 1%R 1%C}. *)

Check bareiss_R.
       (* (forall (m1₁ m1₂ : nat) (m1_R : nat_R m1₁ m1₂)  *)
       (*         (m2₁ m2₂ : nat) (m2_R : nat_R m2₁ m2₂) 
                  (n1₁ n1₂ : nat) (n1_R : nat_R n1₁ n1₂) 
                  (n2₁ n2₂ : nat) (n2_R : nat_R n2₁ n2₂) *)
       (*    (H  : mxpolyR₁ (m1₁ + m2₁)%N (n1₁ + n2₁)%N) *)
       (*    (H0 : mxpolyR₂ (m1₂ + m2₂)%N (n1₂ + n2₂)%N), *)
       (*  mxpolyR_R (m1₁ + m2₁)%N (m1₂ + m2₂)%N (addn_R m1_R m2_R) *)
       (*            (n1₁ + n2₁)%N (n1₂ + n2₂)%N (addn_R n1_R n2_R) 
                     M1 M2 -> *)
       (*  mxpolyR_R m1₁ m1₂ m1_R n2₁ n2₂ n2_R 
             (ursubmx  m1₁ m2₁ n1₁ n2₁ M1) *)
       (*    (ursubmxC m1₂ m2₂ n1₂ n2₂ M2)) -> *)

Context `{ursubmxC : ursubmx_of mxpolyC}.

(* Context `{forall m1 m2 n1 n2, *)
(*   refines (RmxpolyC ==> RmxpolyC) *)
(*           (@ursubmx {poly R} m1 m2 n1 n2) 
             (@ursubmxC m1 m2 n1 n2)}. *)


(* Context `{ *)
(*           !refines (nat_R ==> nat_R ==> nat_R ==> nat_R ==> *)
(*                    RmxpolyC ==> RmxpolyC) *)
(*                   (ursubmx poly R}) (@ursubmxC)}. *)

Context `{dlsubmxC : dlsubmx_of mxpolyC}.
(* Context `{forall m1 m2 n1 n2, *)
(*           refines (RmxpolyC ==> RmxpolyC) *)
(*                   (@dlsubmx {poly R} m1 m2 n1 n2) (@dlsubmxC m1 m2 n1 n2)}. *)

Context `{drsubmxC : drsubmx_of mxpolyC}.
(* Context `{forall m1 m2 n1 n2, *)
(*           refines (RmxpolyC ==> RmxpolyC) *)
(*                   (@drsubmx {poly R} m1 m2 n1 n2) (@drsubmxC m1 m2 n1 n2)}. *)

Context `{!hmul_of mxpolyC}.
(* Context `{forall m n p, *)
(*           refines (RmxpolyC ==> RmxpolyC ==> RmxpolyC) *)
(*                   (@mulmx _ m n p) *)
(*                   (@hmul_op _ _ _ m n p)}. *)

Context `{subC : forall m n, sub_of (mxpolyC m n)}.
(* Context `{forall m n, *)
(*           refines (RmxpolyC ==> RmxpolyC ==> RmxpolyC) *)
(*                   (fun M N => M - N) *)
(*                   (@subC m n)}. *)

Context `{scaleC : forall m n, scale_of polyC (mxpolyC m n)}.
(* Context `{forall m n, *)
(*           refines (RpolyC ==> RmxpolyC) *)
(*                   *:%R (@scaleC m n)}. *)


Context `{map_mxC : forall m n, map_mx_of polyC (mxpolyC m n)}.

Context `{top_leftC : forall m, top_left_of (mxpolyC (1 + m) (1 + m)) polyC}.

Context `{divpC : div_of polyC}.

Context `{headC : lead_coef_of C polyC}.

(* Lemma refl_nat_R : forall m, nat_R m m. *)
(* Proof. elim=> [|n]; [ exact: O_R | exact: S_R ]. Qed. *)

Local Instance refines_refl_nat : forall m, refines nat_R m m | 999.
Proof. by rewrite refinesE; apply: refl_nat_R. Qed.


Print prod_hrel.
Print prod_R.
(* Definition prod_hrel A A' B B' (rA : A -> A' -> Type) (rB : B -> B' -> Type) : *)
(*   A * B -> A' * B' -> Type := *)
(*   fun x y => (rA x.1 y.1 * rB x.2 y.2)%type. *)
Check bareiss_rec_R.

(* Definition mxpolyR_R *)
(*      : forall m1 m2 : nat, nat_R m1 m2 -> *)
(*        forall n1 n2 : nat, nat_R n1 n2 -> *)
(*        'M[R]_(m1,n1) -> mxpolyC m2 n2 -> Type. *)
(* move=> m1 m2 hm n1 n2 hn. *)
(* case: hm. *)



Global Instance refines_bareiss_rec m :
   refines (RpolyC ==> RmxpolyC ==> RpolyC)
     (@bareiss_rec {poly R} (matrix {poly R}) _ _ _ _ _ _ _ _ _ m)
     (@bareiss_rec polyC mxpolyC _ _ _ _ _ _ _ _ _ m).
Proof.
  rewrite refinesE; do?move=> ?*.
  eapply (bareiss_rec_R)=> //; intros.
eapply refinesP; tc.
eapply refines_apply; tc.
Check ?mxpolyR_R.
clear X1 X0 X.

rewrite /ursubmx_of_instance_0.
simpl.
eapply refines_apply; tc.
move=> m1 m2 h1.
move=> n1 n2 h2.
intros.
Check ?mxpolyR_R.

=> // *; eapply refinesP;
  do ?eapply refines_apply; tc.



param bareiss_rec_R.
rewrite /ursubmx_of_instance_0.
eapply H1.
tc.

eapply refines_apply.
eapply refinesP.
intros.
eapply H1.
Admitted.

End bareiss_param.
End bareiss_correctness.


(* Test computations *)

(*    WARNING never use compute, but vm_compute, *)
(*    otherwise it's painfully slow *)
(* Require Import ZArith Zinfra. *)
(* Section test. *)

(* Definition excp n (M: Matrix [cringType Z of Z]) := ex_char_poly_mx n M. *)

(* Definition idZ n := @ident _ [cringType Z of Z] n. *)

(* Definition cpmxid2 := (excp 2 (idZ 2)). *)
(* Definition cpid2 := (exBareiss_rec 2 [:: 1%Z] cpmxid2). *)

(* Eval vm_compute in cpid2. *)

(* Definition detid2 := horner_seq cpid2 0%Z. *)

(* Eval vm_compute in detid2. *)

(* Definition M2 := cM 19%Z [:: 3%Z] [:: (-2)%Z] (cM 26%Z [::] [::] (@eM _ _)). *)

(* Definition cpmxM2 := excp 2 M2. *)
(* Definition cpM2 := exBareiss 2 cpmxM2. *)

(* Eval vm_compute in cpM2. *)
(* Eval vm_compute in ex_bdet 2 M2. *)

(* (* Random 3x3 matrix *) *)
(* Definition M3 := *)
(*   cM 10%Z [:: (-42%Z); 13%Z] [:: (-34)%Z; 77%Z] *)
(*      (cM 15%Z [:: 76%Z] [:: 98%Z] *)
(*          (cM 49%Z [::] [::] (@eM _ _))). *)

(* Time Eval vm_compute in ex_bdet 3 M3. *)

(* (* Random 10x10 matrix *) *)
(* Definition M10 := cM (-7)%Z [:: (-12)%Z ; (-15)%Z ; (-1)%Z ; (-8)%Z ; (-8)%Z ; 19%Z ; (-3)%Z ; (-8)%Z ; 20%Z] [:: 5%Z ; (-14)%Z ; (-12)%Z ; 19%Z ; 20%Z ; (-5)%Z ; (-3)%Z ; 8%Z ; 16%Z] (cM 1%Z [:: 16%Z ; (-18)%Z ; 8%Z ; (-13)%Z ; 18%Z ; (-6)%Z ; 10%Z ; 6%Z] [:: 5%Z ; 4%Z ; 0%Z ; 4%Z ; (-18)%Z ; (-19)%Z ; (-2)%Z ; 3%Z] (cM (-8)%Z [:: 1%Z ; (-10)%Z ; 12%Z ; 0%Z ; (-14)%Z ; 18%Z ; (-5)%Z] [:: (-14)%Z ; (-10)%Z ; 15%Z ; 0%Z ; 13%Z ; (-12)%Z ; (-16)%Z] (cM (-13)%Z [:: (-2)%Z ; (-14)%Z ; (-11)%Z ; 15%Z ; (-1)%Z ; 8%Z] [:: 6%Z ; 9%Z ; (-19)%Z ; (-19)%Z ; (-16)%Z ; (-10)%Z] (cM (-12)%Z [:: 1%Z ; (-5)%Z ; 16%Z ; 5%Z ; 6%Z] [:: 16%Z ; (-20)%Z ; 19%Z ; 16%Z ; 5%Z] (cM 2%Z [:: (-10)%Z ; (-3)%Z ; (-17)%Z ; 18%Z] [:: 4%Z ; (-4)%Z ; 20%Z ; (-7)%Z] (cM 4%Z [:: (-8)%Z ; 2%Z ; 9%Z] [:: 17%Z ; 10%Z ; 10%Z] (cM (-15)%Z [:: 16%Z ; 3%Z] [:: 5%Z ; (-1)%Z] (cM 3%Z [:: 4%Z] [:: (-12)%Z] ((@eM _ _)))))))))). *)

(* Time Eval vm_compute in ex_bdet 10 M10. *)

(* (* *)
(* (* Random 20x20 matrix *) *)
(* Definition M20 := cM (-17)%Z [:: 4%Z ; 9%Z ; 4%Z ; (-7)%Z ; (-4)%Z ; 16%Z ; (-13)%Z ; (-6)%Z ; (-4)%Z ; (-9)%Z ; 18%Z ; 7%Z ; 3%Z ; (-14)%Z ; 8%Z ; (-17)%Z ; 17%Z ; (-2)%Z ; 8%Z] [:: 0%Z ; 10%Z ; 17%Z ; (-7)%Z ; 3%Z ; 18%Z ; (-3)%Z ; 6%Z ; 2%Z ; (-7)%Z ; (-3)%Z ; 16%Z ; 7%Z ; (-9)%Z ; 15%Z ; (-17)%Z ; (-9)%Z ; (-18)%Z ; 9%Z] (cM 13%Z [:: (-3)%Z ; 9%Z ; 7%Z ; 4%Z ; 18%Z ; 2%Z ; 7%Z ; 9%Z ; (-10)%Z ; 18%Z ; 4%Z ; 13%Z ; (-16)%Z ; (-5)%Z ; 6%Z ; (-14)%Z ; 3%Z ; 12%Z] [:: 14%Z ; (-15)%Z ; 14%Z ; (-7)%Z ; 11%Z ; 10%Z ; (-10)%Z ; 9%Z ; (-4)%Z ; (-7)%Z ; (-4)%Z ; 7%Z ; (-10)%Z ; 15%Z ; (-4)%Z ; 12%Z ; (-18)%Z ; 4%Z] (cM 16%Z [:: (-5)%Z ; 8%Z ; 4%Z ; 8%Z ; 4%Z ; (-18)%Z ; 10%Z ; 3%Z ; (-12)%Z ; 12%Z ; 8%Z ; 11%Z ; (-12)%Z ; (-1)%Z ; 12%Z ; (-5)%Z ; (-10)%Z] [:: 1%Z ; (-15)%Z ; (-3)%Z ; (-3)%Z ; 6%Z ; (-3)%Z ; 18%Z ; 6%Z ; (-6)%Z ; (-10)%Z ; 15%Z ; 11%Z ; 6%Z ; (-4)%Z ; (-4)%Z ; 9%Z ; (-3)%Z] (cM (-12)%Z [:: 1%Z ; 6%Z ; 7%Z ; 5%Z ; 0%Z ; (-2)%Z ; 2%Z ; 14%Z ; 15%Z ; (-10)%Z ; (-14)%Z ; (-6)%Z ; 3%Z ; 17%Z ; (-11)%Z ; (-8)%Z] [:: (-15)%Z ; (-8)%Z ; 5%Z ; 18%Z ; 15%Z ; (-14)%Z ; 13%Z ; 17%Z ; 12%Z ; 16%Z ; (-18)%Z ; 13%Z ; 14%Z ; 17%Z ; (-8)%Z ; (-9)%Z] (cM (-17)%Z [:: (-12)%Z ; (-14)%Z ; (-7)%Z ; (-1)%Z ; 14%Z ; (-14)%Z ; (-13)%Z ; (-4)%Z ; 18%Z ; 13%Z ; (-9)%Z ; 15%Z ; (-10)%Z ; 18%Z ; 14%Z] [:: 8%Z ; (-14)%Z ; 9%Z ; 16%Z ; (-3)%Z ; (-8)%Z ; 9%Z ; (-9)%Z ; (-13)%Z ; 4%Z ; 15%Z ; 15%Z ; 6%Z ; (-14)%Z ; (-6)%Z] (cM 9%Z [:: 4%Z ; (-6)%Z ; 5%Z ; (-3)%Z ; (-6)%Z ; 18%Z ; 2%Z ; 10%Z ; 9%Z ; 17%Z ; (-12)%Z ; (-9)%Z ; 1%Z ; (-2)%Z] [:: (-10)%Z ; (-2)%Z ; 17%Z ; 14%Z ; 1%Z ; (-16)%Z ; 17%Z ; 18%Z ; (-3)%Z ; 4%Z ; (-14)%Z ; 17%Z ; 10%Z ; 7%Z] (cM 16%Z [:: (-15)%Z ; (-15)%Z ; (-18)%Z ; (-12)%Z ; 15%Z ; 7%Z ; (-11)%Z ; (-7)%Z ; (-8)%Z ; (-3)%Z ; (-17)%Z ; (-17)%Z ; (-12)%Z] [:: (-8)%Z ; 4%Z ; 12%Z ; (-7)%Z ; (-11)%Z ; 13%Z ; (-16)%Z ; 7%Z ; 16%Z ; (-1)%Z ; 16%Z ; 3%Z ; (-9)%Z] (cM (-15)%Z [:: 0%Z ; (-12)%Z ; 0%Z ; 16%Z ; 13%Z ; (-5)%Z ; 4%Z ; 1%Z ; 13%Z ; 11%Z ; 0%Z ; 16%Z] [:: 0%Z ; (-17)%Z ; (-10)%Z ; (-6)%Z ; 7%Z ; (-1)%Z ; 17%Z ; 8%Z ; 8%Z ; (-15)%Z ; (-16)%Z ; (-18)%Z] (cM 5%Z [:: 8%Z ; (-17)%Z ; (-15)%Z ; 0%Z ; 8%Z ; 1%Z ; (-2)%Z ; 14%Z ; 14%Z ; (-1)%Z ; (-7)%Z] [:: 14%Z ; (-11)%Z ; (-4)%Z ; (-18)%Z ; (-10)%Z ; (-11)%Z ; (-10)%Z ; (-6)%Z ; (-14)%Z ; (-13)%Z ; 5%Z] (cM (-7)%Z [:: 1%Z ; (-3)%Z ; (-7)%Z ; (-1)%Z ; 2%Z ; 14%Z ; 13%Z ; 7%Z ; 17%Z ; 7%Z] [:: 0%Z ; 1%Z ; (-7)%Z ; 12%Z ; (-1)%Z ; (-5)%Z ; (-12)%Z ; (-7)%Z ; 8%Z ; (-4)%Z] (cM 15%Z [:: (-18)%Z ; (-17)%Z ; 6%Z ; 1%Z ; (-13)%Z ; (-12)%Z ; 4%Z ; 13%Z ; 11%Z] [:: 12%Z ; 2%Z ; (-7)%Z ; (-18)%Z ; 0%Z ; 13%Z ; (-15)%Z ; (-16)%Z ; (-2)%Z] (cM 5%Z [:: (-9)%Z ; (-11)%Z ; 14%Z ; (-6)%Z ; (-11)%Z ; (-15)%Z ; (-12)%Z ; (-4)%Z] [:: (-12)%Z ; 8%Z ; (-8)%Z ; (-14)%Z ; 9%Z ; 3%Z ; 14%Z ; 3%Z] (cM (-18)%Z [:: 16%Z ; (-1)%Z ; 3%Z ; 11%Z ; 9%Z ; (-9)%Z ; 14%Z] [:: (-2)%Z ; (-7)%Z ; (-1)%Z ; 6%Z ; (-16)%Z ; 1%Z ; 6%Z] (cM 3%Z [:: (-8)%Z ; (-1)%Z ; (-1)%Z ; 15%Z ; 10%Z ; 6%Z] [:: 3%Z ; 7%Z ; 15%Z ; 12%Z ; 8%Z ; 5%Z] (cM (-14)%Z [:: (-2)%Z ; (-5)%Z ; 8%Z ; (-9)%Z ; 10%Z] [:: 12%Z ; 0%Z ; (-3)%Z ; 11%Z ; (-2)%Z] (cM 6%Z [:: (-8)%Z ; (-4)%Z ; (-9)%Z ; (-1)%Z] [:: 2%Z ; 5%Z ; (-8)%Z ; 0%Z] (cM (-14)%Z [:: (-8)%Z ; (-2)%Z ; 16%Z] [:: 11%Z ; 2%Z ; (-2)%Z] (cM 16%Z [:: (-14)%Z ; 9%Z] [:: (-17)%Z ; 8%Z] (cM (-18)%Z [:: (-11)%Z] [:: (-14)%Z] ((@eM _ _)))))))))))))))))))). *)

(* Time Eval vm_compute in ex_bdet 20 M20. *)

(*      = 75728050107481969127694371861%Z *)
(*      : CZmodule.Pack (Phant Z_comRingType) (CRing.class Z_cringType) *)
(*          Z_cringType *)
(* Finished transaction in 63. secs (62.825904u,0.016666s) *)
(* *) *)

(* End test. *)

(* Extraction Language Haskell. *)
(*  Extraction "Bareiss" ex_bdet. *)
