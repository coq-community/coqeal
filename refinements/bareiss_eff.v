
Section bareiss_param.

Local Open Scope rel_scope.

Context (C : Type) (rC : R -> C -> Type).
Context (polyC : Type) (RpolyC : {poly R} -> polyC -> Type).
Context (mxC : nat -> nat -> Type)
        (RmxC : forall m1 m2, nat_R m1 m2 ->
                forall n1 n2, nat_R n1 n2 ->
                'M[R]_(m1, n1) -> mxC m2 n2 -> Type).
Arguments RmxC {_ _} _ {_ _} _ _ _.
(* Cyril: bug *)
(*Arguments RmxC {_ _ _ _ _ _} _ _. *)
Context (mxpolyC : nat -> nat -> Type)
        (RmxpolyC : forall m1 m2, nat_R m1 m2 ->
                    forall n1 n2, nat_R n1 n2 ->
                    'M[{poly R}]_(m1, n1) -> mxpolyC m2 n2 -> Type).
Arguments RmxpolyC {_ _} _ {_ _} _ _ _.
(* Cyril: bug *)
(* Arguments RmxpolyC {_ _ _ _ _ _} _ _. *)
Context `{zero_of C, one_of polyC}.
Context `{forall m n, opp_of (mxC m n)}.
Context `{ursubmxC : ursubmx_of mxpolyC}.
Context `{dlsubmxC : dlsubmx_of mxpolyC}.
Context `{drsubmxC : drsubmx_of mxpolyC}.
Context `{!hmul_of mxpolyC}.
Context `{subC : forall m n, sub_of (mxpolyC m n)}.
Context `{forall m n, scale_of polyC (mxpolyC m n)}.
Context `{map_mxC : forall m n, map_mx_of polyC polyC (mxpolyC m n) (mxpolyC m n)}.
Context `{top_leftC : forall m, top_left_of (mxpolyC (1 + m) (1 + m)) polyC}.
Context `{divpC : div_of polyC}.
Variable char_poly_mxC : forall n, mxC n n -> mxpolyC n n.
Variable headC : polyC -> C.
Context `{!refines rC 0%R 0%C, !refines RpolyC 1%R 1%C}.
Context `{forall m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2),
          refines (RmxC rm rn ==> RmxC rm rn) -%R -%C}.
Context `{forall m11 m12 (rm1 : nat_R m11 m12) m21 m22 (rm2 : nat_R m21 m22)
                 n11 n12 (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22),
          refines (RmxpolyC (addn_R rm1 rm2) (addn_R rn1 rn2) ==>
                            RmxpolyC rm1 rn2) (@ursubmx m11 m21 n11 n21)
                  (@ursubmxC m12 m22 n12 n22)}.
Context `{forall m11 m12 (rm1 : nat_R m11 m12) m21 m22 (rm2 : nat_R m21 m22)
                 n11 n12 (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22),
          refines (RmxpolyC (addn_R rm1 rm2) (addn_R rn1 rn2)==>
                            RmxpolyC rm2 rn1) (@dlsubmx m11 m21 n11 n21)
                  (@dlsubmxC m12 m22 n12 n22)}.
Context `{forall m11 m12 (rm1 : nat_R m11 m12) m21 m22 (rm2 : nat_R m21 m22)
                 n11 n12 (rn1 : nat_R n11 n12) n21 n22 (rn2 : nat_R n21 n22),
          refines (RmxpolyC (addn_R rm1 rm2) (addn_R rn1 rn2) ==>
                            RmxpolyC rm2 rn2) (@drsubmx m11 m21 n11 n21)
                  (@drsubmxC m12 m22 n12 n22)}.
Context `{forall m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
                 p1 p2 (rp : nat_R p1 p2),
          refines (RmxpolyC rm rn ==> RmxpolyC rn rp ==> RmxpolyC rm rp) mulmx
                  (@hmul_op _ _ _ m2 n2 p2)}.
Context `{forall m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2),
          refines (RmxpolyC rm rn ==> RmxpolyC rm rn ==> RmxpolyC rm rn)
                  (fun M N => M - N) sub_op}.
Context `{forall m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2),
          refines (RpolyC ==> RmxpolyC rm rn ==> RmxpolyC rm rn) *:%R *:%C}.
Context `{forall m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2),
          refines ((RpolyC ==> RpolyC) ==> RmxpolyC rm rn ==> RmxpolyC rm rn)
                  (fun f => @matrix.map_mx _ _ f m1 n1) (@map_mxC m2 n2)}.
Context `{forall m1 m2 (rm : nat_R m1 m2),
          refines (RmxpolyC (nat_R_S_R rm) (nat_R_S_R rm) ==> RpolyC)
                  (@top_left m1) (@top_leftC m2)}.
Context `{!refines (RpolyC ==> RpolyC ==> RpolyC) (@rdivp R) divpC}.
Context `{forall n1 n2 (rn : nat_R n1 n2),
          refines (RmxC rn rn ==> RmxpolyC rn rn) (@char_poly_mx _ n1)
                  (@char_poly_mxC n2)}.
Context `{!refines (RpolyC ==> rC) head headC}.

Global Instance RpolyC_bareiss_rec m1 m2 (rm : nat_R m1 m2) :
  refines (RpolyC ==> RmxpolyC (nat_R_S_R rm) (nat_R_S_R rm) ==> RpolyC)
          (bareiss_rec (polyR:={poly R}) (mxpolyR:=matrix {poly R}) (m:=m1))
          (bareiss_rec (polyR:=polyC) (mxpolyR:=mxpolyC) (m:=m2)).
Proof. param bareiss_rec_R. Qed.

Global Instance refine_bareiss_rec m :
  refines (RpolyC ==> RmxpolyC (nat_R_S_R (nat_Rxx m)) (nat_R_S_R (nat_Rxx m))
                  ==> RpolyC)
          (bareiss_rec (polyR:={poly R}) (mxpolyR:=matrix {poly R}) (m:=m))
          (bareiss_rec (polyR:=polyC) (mxpolyR:=mxpolyC) (m:=m)).
Proof. exact: RpolyC_bareiss_rec. Qed.

Global Instance RpolyC_bareiss n1 n2 (rn : nat_R n1 n2) :
  refines (RmxpolyC (nat_R_S_R rn) (nat_R_S_R rn) ==> RpolyC)
          (bareiss (polyR:={poly R}) (mxpolyR:=matrix {poly R}) (n:=n1))
          (bareiss (polyR:=polyC) (mxpolyR:=mxpolyC) (n:=n2)).
Proof. param bareiss_R. Qed.

Global Instance refine_bareiss n :
  refines (RmxpolyC (nat_R_S_R (nat_Rxx n)) (nat_R_S_R (nat_Rxx n)) ==> RpolyC)
          (bareiss (polyR:={poly R}) (mxpolyR:=matrix {poly R}) (n:=n))
          (bareiss (polyR:=polyC) (mxpolyR:=mxpolyC) (n:=n)).
Proof. exact: RpolyC_bareiss. Qed.

Global Instance RpolyC_bareiss_char_poly n1 n2 (rn : nat_R n1 n2) :
  refines (RmxC (nat_R_S_R rn) (nat_R_S_R rn) ==> RpolyC)
          (bareiss_char_poly (polyR:={poly R}) (mxR:=matrix R)
                             (mxpolyR:=matrix {poly R}) (@char_poly_mx R)
                             (n:=n1))
          (bareiss_char_poly (polyR:=polyC) (mxR:=mxC) (mxpolyR:=mxpolyC)
                             char_poly_mxC (n:=n2)).
Proof. param bareiss_char_poly_R. Qed.

Global Instance refine_bareiss_char_poly n :
  refines (RmxC (nat_R_S_R (nat_Rxx n)) (nat_R_S_R (nat_Rxx n)) ==> RpolyC)
          (bareiss_char_poly (polyR:={poly R}) (mxR:=matrix R)
                             (mxpolyR:=matrix {poly R}) (@char_poly_mx R)
                             (n:=n))
          (bareiss_char_poly (polyR:=polyC) (mxR:=mxC) (mxpolyR:=mxpolyC)
                             char_poly_mxC (n:=n)).
Proof. exact: RpolyC_bareiss_char_poly. Qed.

Global Instance RC_bdet n1 n2 (rn : nat_R n1 n2) :
  refines (RmxC (nat_R_S_R rn) (nat_R_S_R rn) ==> rC)
          (bdet (R:=R) (polyR:={poly R}) (mxR:=matrix R)
                (mxpolyR:=matrix {poly R}) (@char_poly_mx R) head
                (n:=n1))
          (bdet (R:=C) (polyR:=polyC) (mxR:=mxC) (mxpolyR:=mxpolyC)
                char_poly_mxC headC (n:=n2)).
Proof. param bdet_R. Qed.

Global Instance refine_bdet n :
  refines (RmxC (nat_R_S_R (nat_Rxx n)) (nat_R_S_R (nat_Rxx n)) ==> rC)
          (bdet (R:=R) (polyR:={poly R}) (mxR:=matrix R)
                (mxpolyR:=matrix {poly R}) (@char_poly_mx R) head
                (n:=n))
          (bdet (R:=C) (polyR:=polyC) (mxR:=mxC) (mxpolyR:=mxpolyC)
                char_poly_mxC headC (n:=n)).
Proof. exact: RC_bdet. Qed.

Global Instance RC_det_bdet n1 n2 (rn : nat_R n1 n2) :
  refines (RmxC (nat_R_S_R rn) (nat_R_S_R rn) ==> rC) determinant
          (bdet (R:=C) (polyR:=polyC) (mxpolyR:=mxpolyC) char_poly_mxC headC
                (n:=n2)).
Proof.
  rewrite refinesE=> M M' HM.
  rewrite -bdetE.
  exact: refinesP.
Qed.

Global Instance refine_det n :
  refines (RmxC (nat_R_S_R (nat_Rxx n)) (nat_R_S_R (nat_Rxx n)) ==> rC)
          determinant (bdet (R:=C) (polyR:=polyC) (mxpolyR:=mxpolyC)
                            char_poly_mxC headC (n:=n)).
Proof. exact: RC_det_bdet. Qed.

End bareiss_param.

(***** WIP below here **********)

End bareiss_correctness.

Section test_bareiss.

From mathcomp Require Import ssrint.
From CoqEAL Require Import binint seqpoly poly_div binord.

Definition M : 'M[int]_(2,2) := \matrix_(i,j < 2) 3%:Z.

Goal \det M == 0.
by coqeal [(\det _)%pattern] vm_compute.
Qed.

Definition detM := [coqeal vm_compute of \det M].

Goal \det (1 : 'M[int]_(3)) = 1.
by coqeal.
Abort.

Definition Madd := \matrix_(i,j < 29) (i + j)%:Z%:P.
Time Definition det_Madd := [coqeal vm_compute of \det Madd].

Definition ctmat1 : 'M[int]__ := \matrix_(i < 3, j < 3)
  (nth [::] [:: [::  1 ; 1 ; 1 ]
              ; [:: -1 ; 1 ; 1 ]
              ; [::  0 ; 0 ; 1 ] ] i)`_j.

Definition det_ctmat1 := [coqeal vm_compute of \det ctmat1].
Definition char_poly_ctmat1 :=
  [coqeal vm_compute of \det _ for char_poly ctmat1].

End test_bareiss.

(* Section poly_op. *)

(* Variable R : comRingType. *)

(* Implicit Types p q : {poly R}. *)

(* Definition prptnl n p := \poly_(j < size p - n) p`_(j + n). *)

(* Lemma prptnl0p p : prptnl 0 p = p. *)
(* Proof. *)
(* rewrite /prptnl subn0 -[RHS]coefK. *)
(* apply/polyP=> i. *)
(* by rewrite !coef_poly addn0. *)
(* Qed. *)

(* Lemma prptnlp0 n : prptnl n 0 = 0. *)
(* Proof. *)
(* rewrite /prptnl size_poly0 sub0n. *)
(* apply/polyP=> i. *)
(* by rewrite coef_poly /= coef0. *)
(* Qed. *)

(* Lemma prptnl_oversize n p : size p <= n -> prptnl n p = 0. *)
(* Proof. *)
(* move=> h; apply/polyP=> i. *)
(* by rewrite coef_poly coef0 ltn_subRL leqNgt ltnS -[size p]addn0 *)
(*            (leq_add h (leq0n _)). *)
(* Qed. *)

(* Lemma prptnl_add n p q : prptnl n (p + q) = prptnl n p + prptnl n q. *)
(* Proof. *)
(* apply/polyP => i; symmetry. *)
(* rewrite /prptnl coefD !coef_poly coefD !ltn_subRL addnC. *)
(* have [H1|H1] := ltnP. *)
(*   have [_|H2] := ltnP; first by rewrite -coefD; have [|/leq_sizeP ->] := ltnP. *)
(*   move/leq_sizeP: (H2) => -> //. *)
(*   by rewrite (size_addl (leq_ltn_trans H2 H1)) H1. *)
(* move/leq_sizeP: (H1) => -> //. *)
(* have [H2|/leq_sizeP -> //] := ltnP; last by rewrite addr0 if_same. *)
(* by rewrite [p + q]addrC (size_addl (leq_ltn_trans H1 H2)) H2. *)
(* Qed. *)

(* Lemma prptnl_opp n p : prptnl n (- p) = - prptnl n p. *)
(* Proof. *)
(* apply/polyP => i. *)
(* rewrite /prptnl coefN !coef_poly coefN size_opp -{2}oppr0. *)
(* by case: ltnP. *)
(* Qed. *)

(* Lemma prptnl_sub n p q : prptnl n (p - q) = prptnl n p - prptnl n q. *)
(* Proof. by rewrite prptnl_add prptnl_opp. Qed. *)

(* Lemma prptnlX n p : prptnl n p = prptnl n.+1 (p * 'X). *)
(* Proof. *)
(* have [/eqP ->|Hpn0] := (boolP (p == 0)); first by rewrite mul0r !prptnlp0. *)
(* apply/polyP => i. *)
(* by rewrite !coef_poly size_mulX ?coefMX // subnS subSKn addnS. *)
(* Qed. *)

(* Lemma prptnlXn n k p : prptnl n p = prptnl (n + k) (p * 'X^k). *)
(* Proof. *)
(* elim: k => [|k ih]; first by rewrite addn0 expr0 mulr1. *)
(* by rewrite addnS exprS mulrCA mulrC -prptnlX. *)
(* Qed. *)

(* Lemma size_prptnl n p : size (prptnl n p) = (size p - n)%N. *)
(* Proof. *)
(* have [/eqP ->|Hpn0] := (boolP (p == 0)); first by rewrite prptnlp0 size_poly0 sub0n. *)
(* have [H|] := (ltnP n (size p)). *)
(*   rewrite size_poly_eq //. *)
(*   suff -> : ((size p - n).-1 + n)%N = (size p).-1 by rewrite lead_coef_eq0. *)
(*   case: (size p) H => // m; rewrite ltnS => H. *)
(*   by rewrite subSKn subnK. *)
(* rewrite /prptnl -subn_eq0 => /eqP ->. *)
(* rewrite -[0%N](@size_poly0 R). *)
(* congr size; congr polyseq. *)
(* apply/polyP => i. *)
(* by rewrite coef_poly size_poly0 coef0. *)
(* Qed. *)

(* Lemma prptnlS n p : prptnl n.+1 p = prptnl 1 (prptnl n p). *)
(* Proof. *)
(* apply/polyP=> i. *)
(* rewrite !coef_poly [(i + 1)%N]addnC -ltn_subRL subnS !subn1 size_prptnl add1n. *)
(* by rewrite addSnnS; case: ltnP. *)
(* Qed. *)

(* Lemma mulXn_prptnl : forall n p q, p * 'X^n = q -> p = prptnl n q. *)
(* Proof. *)
(* elim=> [p q|n ih p q h]; first by rewrite expr0 mulr1 prptnl0p => ->. *)
(* rewrite prptnlS -(ih (p * 'X)); first by rewrite -prptnlX prptnl0p. *)
(* by rewrite -mulrA -exprS. *)
(* Qed. *)

(* (* Key property - maybe it should be expressed with rdivp... *) *)
(* Lemma test n p q r : p * 'X^n = q + r -> size r <= n -> p = prptnl n q. *)
(* Proof. *)
(* move=> h_eq sr. *)
(* by rewrite (mulXn_prptnl h_eq) prptnl_add (prptnl_oversize sr) addr0. *)
(* Qed. *)

(* Lemma prptnlK m n p : prptnl m (prptnl n p) = prptnl (m + n) p. *)
(* Proof. *)
(* apply/polyP => i. *)
(* rewrite !coef_poly {1}addnC -ltn_subRL {1}[(m + n)%N]addnC subnDA size_prptnl. *)
(* by rewrite addnA; case: ltnP. *)
(* Qed. *)

(* Lemma prptnl_mulC n d p : prptnl n (d%:P * p) = d%:P * prptnl n p. *)
(* Proof. *)
(* elim/poly_ind: p n => [n|p c ih [|n]]; first by rewrite mulr0 !prptnlp0 mulr0. *)
(*   by rewrite !prptnl0p. *)
(* rewrite mulrDr !prptnl_add mulrDr mulrA -!prptnlX ih -polyC_mul. *)
(* rewrite ![prptnl n.+1 _%:P]prptnl_oversize ?mulr0 ?addr0 // size_polyC. *)
(*   by case: (c == 0). *)
(* by case: (d * c == 0). *)
(* Qed. *)

(* (* Lemma prptnlC : forall n c, prptnl n c%:P =  *) *)


(* Lemma prptnl_mul n p q : prptnl (size p + n) (p * q) = *)
(*                          prptnl (size p) (p * prptnl n q). *)
(* Proof. *)
(* elim/poly_ind: p q n=> [|p c ih] q n; first by rewrite !mul0r !prptnlp0. *)
(* have [/eqP ->|Hpn0] := (boolP (p == 0)). *)
(*   by rewrite mul0r add0r !prptnl_mulC prptnlK. *)
(* rewrite !mulrDl !prptnl_add size_addl size_mulX //; last first. *)
(*   rewrite size_polyC ltnS. *)
(*   by case: (c == 0) => //=; rewrite lt0n size_eq0 -polyseq0. *)
(* rewrite mulrC mulrA -prptnlX mulrC ih // -mulrA ['X * _]mulrC mulrA. *)
(* by rewrite -prptnlX -prptnl_mulC prptnlK addSn. *)
(* Qed. *)

(* (* Lemma prptnl_monic : forall n p, prptnl n p \is monic = (p \is monic). *) *)
(* (* Proof. *) *)
(* (* move => n. *) *)
(* (* elim/poly_ind. *) *)
(* (*   by rewrite prptnlp0. *) *)
(* (* move=> p c ih. *) *)
(* (* rewrite prptnl_add !monicE. *) *)
(* (* admit. *) *)
(* (* Qed. *) *)

(* Definition pmul (n : nat) p q := prptnl n (p * q). *)

(* Lemma pmulP : forall n p q, pmul n p q = prptnl n (p * q). *)
(* Admitted. *)

(* Fixpoint sasaki_rec m (a : {poly R}) : 'M[{poly R}]_(1 + m) -> {poly R} := *)
(*   match m return 'M[_]_(1 + m) -> {poly R} with *)
(*     | S p => fun (M: 'M[_]_(1 + _)) => *)
(*       let d   := M 0 0 in *)
(*       let l   := ursubmx M in *)
(*       let c   := dlsubmx M in *)
(*       let N   := drsubmx M in *)
(*       let M'  := \matrix_(i,j) (pmul (size a).-2 d (N i j) - *)
(*                                 pmul (size a).-2 (c i 0) (l 0 j)) in *)
(*       let q   := rdivp 'X^(size a).*2.+1 a in *)
(*       let M'' := map_mx (fun x => pmul ((size a).+3 - (size a == 1))%N q x) M' in *)
(*         sasaki_rec d M'' *)
(*     | _ => fun M => M 0 0 *)
(*   end. *)

(* Definition sasaki_char_poly n (M : 'M[R]_(1 + n)) := sasaki_rec 1 (char_poly_mx M). *)

(* (* Lemma size_rdivp : forall p q, p \is monic -> rdvdp p q -> size (rdivp q p) = (size q - (size p).-1)%N. *) *)
(* (* Proof. *) *)
(* (* move=> p q pm hdvd. *) *)

(* (* admit. *) *)
(* (* Qed. *) *)

(* (* Lemma test_size : forall m (a : {poly R}) (M : 'M[{poly R}]_(1 + m)), *) *)
(* (*   a \is monic ->  *) *)
(* (*   M 0 0 \is monic -> *) *)
(* (*   (forall i j, rdvdp (R:=R) a *) *)
(* (*    (M 0 0 * M (lift 0 i) (lift 0 j) - M (lift 0 i) 0 * M 0 (lift 0 j))) -> *) *)
(* (*  (* (forall i, size (M i i) = (size a).+2)%N ->   *) *) *)
(* (*  (* (forall i j, size (M j i * M i j) * (i != j) < size (M i i * M j j)) -> *) *) *)
(* (*  (forall i j, if i == j then size (M i i) = (size a).+2  *) *)
(* (*                         else (M i j == 0) || (size (M i j) == (size a).-1)) -> *) *)
(* (*   forall i j, size (rdivp (M 0 0 * M (lift 0 i) (lift 0 j) -  *) *)
(* (*                            M (lift 0 i) 0 * M 0 (lift 0 j)) a) <= (size a).+2. *) *)
(* (* Proof. *) *)
(* (* move=> m a /= M am m00 hdvd h1 /= i j. *) *)
(* (* rewrite size_rdivp //. *) *)
(* (* rewrite size_addl. *) *)
(* (* case hij: (i == j). *) *)
(* (*   rewrite (eqP hij). *) *)
(* (*   rewrite size_monicM //. *) *)
(* (*   move: (h1 0 0). *) *)
(* (*   rewrite eqxx => -> /=. *) *)
(* (*   move: (h1 (lift 0 j) (lift 0 j)). *) *)
(* (*   rewrite eqxx => ->. *) *)
(* (*   admit. *) *)
(* (* admit. *) *)
(* (* admit. *) *)
(* (* rewrite size_opp. *) *)
(* (* case h000: (M (lift 0 i) (lift 0 j) == 0). *) *)
(* (*   (* by rewrite (eqP h000) mulr0 size_poly0 sub0n. *) *) *)
(* (*   admit. *) *)
(* (* rewrite [size (M 0 0 * _)]size_monicM //. *) *)
(* (* admit. *) *)
(* (* admit. *) *)

(* (* Qed. *) *)

(* (* Lemma sasaki_recE : forall m (a : {poly R}) (M : 'M[{poly R}]_(1 + m)), *) *)
(* (*   a \is monic ->  *) *)
(* (*  (forall (p : nat) (h h' : p < 1 + m), pminor h h' M \is monic) -> *) *)
(* (*  (forall k (f g : 'I_k.+1 -> 'I_m.+1), rdvdp (a ^+ k) (minor f g M)) -> *) *)
(* (*  (forall i, size (M i i) = (size a).+2)%N -> *) *)
(* (*  (forall i j, size (M j i * M i j) * (i != j) < size (M i i * M j j)) -> *) *)
(* (*  (* (forall (f g : 'I_2 -> 'I_m.+1), size (minor f g M) <= (size a).+2) -> *) *) *)
(* (*   sasaki_rec a M = bareiss_rec a M. *) *)
(* (* Proof. *) *)
(* (* elim=> //= m ih a M am hpm hdvdk hsize1 hsize2. *) *)
(* (* case: (bareiss_invariants am hpm hdvdk). *) *)
(* (* set d := M 0 0; set M' := _ - _; set M'' := map_mx _ _; simpl in M' => h1 h2 h3 h4. *) *)
(* (* suff -> : map_mx *) *)
(* (*      [eta pmul ((size a).+3 - (size a == 1)%N) *) *)
(* (*             (rdivp (R:=R) 'X^(size a).*2.+1 a)] *) *)
(* (*      (\matrix_(i, j) (pmul (size a).-2 (M 0 0) ((drsubmx M) i j) - *) *)
(* (*                       pmul (size a).-2 ((dlsubmx M) i 0) ((ursubmx M) 0 j))) = *) *)
(* (*    map_mx ((rdivp (R:=R))^~ a) (M 0 0 *: drsubmx M - dlsubmx M *m ursubmx M). *) *)
(* (*   rewrite ih //. *) *)

(* (* move=> i. *) *)
(* (* rewrite -/M'. *) *)
(* (* rewrite !mxE !big_ord1 !mxE !lshift0 !rshift1 /d size_rdivp //; last first. *) *)
(* (*   pose f := fun (x : 'I_2) => if x == 0 then 0 else (lift 0 i). *) *)
(* (*   have := (@hdvdk _ f f). *) *)
(* (*   by rewrite minor2 /f /= expr1. *) *)
(* (* rewrite (hsize1 0). *) *)
(* (* rewrite size_addl; last first. *) *)
(* (*   rewrite size_opp. *) *)
(* (*   move: (hsize2 0 (lift 0 i)). *) *)
(* (*   by rewrite /= muln1. *) *)
(* (* case H0 : (M (lift 0 i) (lift 0 i) == 0). *) *)
(* (* move: (hsize1 (lift 0 i)). *) *)
(* (* by rewrite (eqP H0) size_poly0. *) *)
(* (* rewrite size_monicM //; last by rewrite H0. *) *)
(* (* rewrite (hsize1 0) (hsize1 (lift 0 i)). *) *)
(* (* simpl. *) *)
(* (* case a0 : (size a == 0)%N. *) *)
(* (*   move: am. *) *)
(* (*   move: a0. *) *)
(* (*   rewrite size_poly_eq0 => /eqP ->. *) *)
(* (*   rewrite monicE. *) *)
(* (*   rewrite lead_coef0. *) *)
(* (*   rewrite eq_sym =>HH. *) *)
(* (*   move: (oner_neq0 R). *) *)
(* (*   by rewrite HH. *) *)
(* (* rewrite -subn1 subnBA; last by rewrite lt0n a0. *) *)
(* (* rewrite addn1 -!addnS. *) *)
(* (* rewrite addnC. *) *)
(* (* rewrite -addnBA. *) *)
(* (* by rewrite subnn addn0. *) *)
(* (* done. *) *)

(* (* admit. *) *)

(* (* apply/matrixP=> i j; rewrite !mxE big_ord1 !pmulP !mxE lshift0 -prptnl_sub !rshift1. *) *)
(* (* have [sa0|an0] := boolP (size a == 0)%N. *) *)
(* (*   rewrite (eqP sa0); move: sa0; rewrite size_poly_eq0 => /eqP -> /=. *) *)
(* (*   by rewrite !rdivp0 mul0r prptnlp0. *) *)
(* (* have a0 : a != 0 by rewrite -size_poly_eq0. *) *)
(* (* set e := M _ _; set N := M _ _; set c := M _ _; set l := M _ _. *) *)

(* (* have hdvd : rdvdp a (d * N - c * l). *) *)
(* (*   move: (hdvdk 1%N) => HHH. *) *)
(* (*   pose f := fun (x : 'I_2) => if x == 0 then 0 else (lift 0 i). *) *)
(* (*   pose g := fun (x : 'I_2) => if x == 0 then 0 else (lift 0 j). *) *)
(* (*   move: (HHH f g). *) *)
(* (*   by rewrite minor2 /f /g /= expr1.  *) *)

(* (* have := (rdivp_eq am ('X^(size a).*2.+1)). *) *)
(* (* set q := rdivp _ _; set r := rmodp _ _; set M''' := rdivp _ _. *) *)
(* (* move=> Hqr. *) *)

(* (* have H1 : M''' * 'X^(size a).*2.+1 = (d * N - c * l) * q + M''' * r. *) *)
(* (*   rewrite Hqr mulrDr. *) *)
(* (*   congr (_ + _). *) *)
(* (*   rewrite mulrC -mulrA mulrC. *) *)
(* (*   congr (_ * _). *) *)
(* (*   rewrite /M' mulrC rdivpK //. *) *)
(* (*   move: am. *) *)
(* (*   by rewrite monicE => /eqP ->; rewrite expr1n mulr1. *) *)

(* (* have := (ltn_rmodpN0 'X^(size a).*2.+1 a0); rewrite -/r => Hr. *) *)

(* (* have q0 : q != 0. *) *)
(* (*   apply/eqP => q0; move: Hqr Hr. *) *)
(* (*   rewrite q0 !mul0r add0r => <-. *) *)
(* (*   by rewrite size_polyXn -addnn -!addnS -{3}[size a]addn0 leq_add2l. *) *)

(* (* have laq0 : lead_coef q * lead_coef a != 0. *) *)
(* (*   have H : GRing.lreg (lead_coef a). *) *)
(* (*     move: am. *) *)
(* (*     rewrite monicE => /eqP ->. *) *)
(* (*     exact: lreg1. *) *)
(* (*   by rewrite mulrC (mulrI_eq0 _ H) lead_coef_eq0. *) *)

(* (* have Hsize : size q = (size a).+3. *) *)
(* (*   have := (size_polyXn R (size a).*2.+1). *) *)
(* (*   rewrite Hqr size_addl size_proper_mul //. *) *)
(* (*     rewrite -addnn -addSn => /eqP. *) *)
(* (*     rewrite -eqSS -!addSn prednK /=. *) *)
(* (*       by rewrite eqn_add2r => /eqP. *) *)
(* (*     by rewrite addn_gt0 !lt0n an0 orbT. *) *)
(* (*   move: q0. *) *)
(* (*   rewrite -size_poly_eq0. *) *)
(* (*   case: (size q) => // n _. *) *)
(* (*   exact: (ltn_addl n Hr). *) *)

(* (* have Hm' : size M''' <= (size a).+2. *) *)
(* (* rewrite /M'''. *) *)
(* (*   (* apply/(leq_trans (leq_rdivp (d * N - c * l) a)). *) *) *)
(* (*   rewrite /e /N /c /l. *) *)
(* (*   rewrite test_size //. *) *)
(* (*   move=> /= x y. *) *)
(* (*   move: (hdvdk 1%N) => HHH. *) *)
(* (*   pose f := fun (apa : 'I_2) => if apa == 0 then 0 else (lift 0 x). *) *)
(* (*   pose g := fun (apa : 'I_2) => if apa == 0 then 0 else (lift 0 y). *) *)
(* (*   move: (HHH f g). *) *)
(* (*   by rewrite minor2 /f /g /= expr1.  *) *)

(* (* have H2 : size (M''' * r) <= (size a).*2.+1. *) *)
(* (*   rewrite (leq_trans (size_mul_leq M''' r)) // -addnn. *) *)
(* (*   have := (leq_add Hm' Hr). *) *)
(* (*   rewrite !addSn addnS ltnS => HH. *) *)
(* (*   have H : (size M''' + size r).-1 <= (size M''' + size r). *) *)
(* (*     by case: (size M''' + size r)%N. *) *)
(* (*   exact: (leq_trans H HH). *) *)

(* (* rewrite (test H1 H2). *) *)
(* (* case sa: (size a == 1)%N. *) *)
(* (*   by rewrite (eqP sa) prptnl0p -addnn mulrC. *) *)
(* (* rewrite subn0 -Hsize -prptnl_mul Hsize mulrC. *) *)
(* (* f_equal. *) *)
(* (* rewrite -addnn !addSn -!addnS prednK. *) *)
(* (*   rewrite prednK //. *) *)
(* (*   by case: (size a) an0. *) *)
(* (* by case: (size a) an0 sa => //= [[]]. *) *)
(* (* Qed.  *) *)


(* (* OLD STUFF BELOW *) *)


(* (* Definition sasaki_char_poly n (M : 'M[R]_(1 + n)) := sasaki_rec 1 (char_poly_mx M). *) *)


(* (* (* Lemma sasakiE : forall m (M : 'M[R]_(1 + m)), sasaki_char_poly M = bareiss_char_poly M. *) *) *)
(* (* (* Proof. *) *) *)
(* (* (* rewrite /sasaki_char_poly /bareiss_char_poly /bareiss. *) *) *)
(* (* (* elim. *) *) *)
(* (* (* move=> M. *) *) *)
(* (* (* simpl. *) *) *)
(* (* (* done. *) *) *)
(* (* (* move=> n ih M. *) *) *)
(* (* (* simpl. *) *) *)
(* (* (* rewrite /bareiss. *) *) *)


(* (* Lemma size_rmodpXn p (p0 : p != 0) : size (rmodp 'X^(size p).*2.+1 p) < (size p). *) *)
(* (* Proof. exact: (ltn_rmodpN0 'X^(size p).*2.+1 p0). Qed. *) *)

(* (* Lemma size_rdivpXn p (pm : p \is monic) : size (rdivp 'X^(size p).*2.+1 p) = (size p).+3. *) *)
(* (* Proof. *) *)
(* (* move: (rdivp_eq pm ('X^(size p).*2.+1)) (ltn_rmodpN0 'X^(size p).*2.+1 (monic_neq0 pm)) *) *)
(* (*       (size_polyXn R (size p).*2.+1). *) *)
(* (* set q := rdivp _ _; set r := rmodp _ _ => -> Hr. *) *)
(* (* rewrite size_addl size_proper_mul //. *) *)
(* (*     rewrite -addnn -addSn => /eqP. *) *)
(* (*     rewrite -eqSS -!addSn prednK /=. *) *)
(* (*       by rewrite eqn_add2r => /eqP. *) *)
(* (*     by rewrite addn_gt0 !lt0n !size_poly_eq0 (monic_neq0 pm) orbT. *) *)
(* (*   admit. *) *)

(* (*   move: (monic_neq0 pm). *) *)
(* (*   rewrite -size_poly_eq0. *) *)
(* (*   case: (size p) => // n _ /=. *) *)
(* (*   rewrite addnS /=. *) *)
(* (*   move: (ltn_addl n Hr). *) *)
(* (*   admit. *) *)
(* (* admit. *) *)
(* (* Qed. *) *)

(* (* Lemma sasaki_recE : forall m (a : {poly R}) (M : 'M[{poly R}]_(1 + m)), *) *)
(* (*   (* (forall (f g : 'I_2 -> 'I_(1 + m)%N), size (minor f g M) <= (size a).+2) -> *) *) *)
(* (*   (* (forall i j, if i == j then size (M i i) == (size a).+1 *) *) *)
(* (*   (*                        else size (M i j) <= size a) -> *) (* THIS DOES NOT WORK!!! *) *) *)
(* (*   a \is monic -> *) *)
(* (*   (forall i, M i i \is monic) -> *) *)
(* (*   (* (forall i j, size (M i i * M j j) == (size a).+2) -> *) *) *)
(* (*   (* (forall i j, size (M 0 i * M j 0) <= size a) -> *) *) *)
(* (*   (* (forall i j, size (M 0 0 * M (lift 0 i) (lift 0 j) - M (lift 0 i) 0 * M 0 (lift 0 j)) <= (size a).+2) -> *) *) *)
(* (*  (* (forall (f g : 'I_2 -> 'I_m.+1), rdvdp a (minor f g M)) -> *) *) *)
(* (*   sasaki_rec a M = bareiss_rec a M. *) *)
(* (* Proof. *) *)
(* (* (* elim=> //= m ih a M hs am hm. *) *) *)
(* (* (* elim=> //= m ih a M am hm hs_diag hs. *) *) *)
(* (* elim=> //= m ih a M am hm. *) *)

(* (* (* have -> : (map_mx *) *) *)
(* (* (*         (fun x : {poly R} => *) *) *)
(* (* (*          if (size a == 1)%N *) *) *)
(* (* (*          then pmul (size a).+2 (rdivp (R:=R) 'X^(size a).*2.+1 a) x *) *) *)
(* (* (*          else pmul (size a).+3 (rdivp (R:=R) 'X^(size a).*2.+1 a) x) *) *) *)
(* (* (*         (\matrix_(i, j) (pmul (size a).-2 (M 0 0) ((drsubmx M) i j) - *) *) *)
(* (* (*                          pmul (size a).-2 ((dlsubmx M) i 0) ((ursubmx M) 0 j)))) = (map_mx ((rdivp (R:=R))^~ a) *) *) *)
(* (* (*         (M 0 0 *: drsubmx M - dlsubmx M *m ursubmx M)); last first. *) *) *)
(* (* (*   admit. *) *) *)


(* (* rewrite ih; last first. *) *)
(* (*   admit. *) *)
(* (*   (* move=> i. *) *) *)
(* (*   (* rewrite !mxE !pmulP -prptnl_sub !lshift0 !rshift1. *) *) *)
(* (*   (* case: ifP => sa1; rewrite prptnl_monic. *) *) *)
(* (*   (* rewrite (eqP sa1) /= prptnl0p. *) *) *)
(* (*   (* admit. *) *) *)
(* (*   (* admit. *) *) *)

(* (* (* simpl. *) *) *)
(* (* (*   move=> i j. *) *) *)
(* (* (*   rewrite !mxE !pmulP -prptnl_sub !lshift0 !rshift1. *) *) *)
(* (* (*   case: ifP => sa1. *) *) *)
(* (* (*   rewrite (eqP sa1) /= !prptnl0p. *) *) *)
(* (* (* Search _ rdivp size. *) *) *)
(* (* (* have -> : lift 0 0 = 1. *) *) *)
(* (* (*   by move=> n; apply/ord_inj. *) *) *)
(* (* (*   admit. *) *) *)
(* (* (*   admit. *) *) *)

(* (* (*   move=> i j. *) *) *)
(* (* (*   rewrite !mxE !pmulP -prptnl_sub !lshift0 !rshift1. *) *) *)
(* (* (*   case: ifP => sa1. *) *) *)
(* (* (*   rewrite (eqP sa1) /= prptnl0p. *) *) *)
(* (* (*   admit. *) *) *)
(* (* (*   admit. *) *) *)

(* (* (*   move=> i. *) *) *)
(* (* (*   rewrite !mxE !pmulP -prptnl_sub !lshift0 !rshift1. *) *) *)
(* (* (*   case: ifP => sa1; rewrite prptnl_monic. *) *) *)
(* (* (*   rewrite (eqP sa1) /= prptnl0p. *) *) *)

(* (* (*     admit. *) *) *)
(* (*   exact: (hm 0). *) *)
(* (* (* move=> f g. *) *) *)
(* (* (* rewrite minor2 !mxE !pmulP -prptnl_sub !lshift0 !rshift1. *) *) *)

(* (* (* case: ifP=> sa. *) *) *)
(* (* (* rewrite (eqP sa) /= !prptnl0p size_addl.  *) *) *)
(* (* (* rewrite size_proper_mul. *) *) *)
(* (* (* rewrite !size_prptnl. *) *) *)
(* (* (* rewrite size_proper_mul. *) *) *)
(* (* (* Search _ size rdivp. *) *) *)

(* (* (* rewrite /minor. *) *) *)
(* (* (* simpl. *) *) *)

(* (* (* move=> i j. *) *) *)
(* (* (* case: ifP=> hij. *) *) *)
(* (* (* rewrite (eqP hij). *) *) *)
(* (* (* rewrite !mxE !pmulP !rshift1 !lshift0 -prptnl_sub. *) *) *)
(* (* (* case: ifP => sa. *) *) *)
(* (* (* set q := rdivp _ _. *) *) *)
(* (* (* set d := M _ _; set N := M _ _; set c := M _ _; set l := M _ _. *) *) *)

(* (* (*   admit. *) *) *)
(* (* (* admit. *) *) *)
(* (* (* admit. *) *) *)

(* (* congr bareiss_rec. *) *)
(* (* apply/matrixP=> i j; rewrite !mxE big_ord1 !pmulP !mxE lshift0 -prptnl_sub !rshift1. *) *)
(* (* have [sa0|an0] := boolP (size a == 0)%N. *) *)
(* (*   rewrite (eqP sa0); move: sa0; rewrite size_poly_eq0 => /eqP -> /=. *) *)
(* (*   by rewrite !rdivp0 mul0r prptnlp0. *) *)
(* (* have a0 : a != 0 by rewrite -size_poly_eq0. *) *)
(* (* set d := M _ _; set N := M _ _; set c := M _ _; set l := M _ _. *) *)

(* (* have hdvd : rdvdp a (d * N - c * l) by admit. *) *)

(* (* have := (rdivp_eq am ('X^(size a).*2.+1)). *) *)
(* (* set q := rdivp _ _; set r := rmodp _ _; set M' := rdivp _ _.  *) *)
(* (* move=> Hqr. *) *)

(* (* have H1 : M' * 'X^(size a).*2.+1 = (d * N - c * l) * q + M' * r. *) *)
(* (*   rewrite Hqr mulrDr. *) *)
(* (*   congr (_ + _). *) *)
(* (*   rewrite mulrC -mulrA mulrC. *) *)
(* (*   congr (_ * _). *) *)
(* (*   rewrite /M' mulrC rdivpK //. *) *)
(* (*   move: am. *) *)
(* (*   by rewrite monicE => /eqP ->; rewrite expr1n mulr1. *) *)

(* (* have := (ltn_rmodpN0 'X^(size a).*2.+1 a0); rewrite -/r => Hr. *) *)

(* (* have q0 : q != 0. *) *)
(* (*   apply/eqP => q0; move: Hqr Hr. *) *)
(* (*   rewrite q0 !mul0r add0r => <-. *) *)
(* (*   by rewrite size_polyXn -addnn -!addnS -{3}[size a]addn0 leq_add2l. *) *)

(* (* have laq0 : lead_coef q * lead_coef a != 0. *) *)
(* (*   have H : GRing.lreg (lead_coef a). *) *)
(* (*     move: am. *) *)
(* (*     rewrite monicE => /eqP ->. *) *)
(* (*     exact: lreg1. *) *)
(* (*   by rewrite mulrC (mulrI_eq0 _ H) lead_coef_eq0. *) *)

(* (* have Hsize : size q = (size a).+3. *) *)
(* (*   have := (size_polyXn R (size a).*2.+1). *) *)
(* (*   rewrite Hqr size_addl size_proper_mul //. *) *)
(* (*     rewrite -addnn -addSn => /eqP. *) *)
(* (*     rewrite -eqSS -!addSn prednK /=. *) *)
(* (*       by rewrite eqn_add2r => /eqP. *) *)
(* (*     by rewrite addn_gt0 !lt0n an0 orbT. *) *)
(* (*   move: q0. *) *)
(* (*   rewrite -size_poly_eq0. *) *)
(* (*   case: (size q) => // n _. *) *)
(* (*   exact: (ltn_addl n Hr). *) *)

(* (* have Hm' : size M' <= (size a).+2. *) *)
(* (*   (* rewrite /M'. *) *) *)
(* (*   (* apply/(leq_trans (leq_rdivp (d * N - c * l) a)). *) *) *)
(* (*   (* rewrite /d /N /c /l. *) *) *)
(* (*   (* rewrite size_addl. *) *) *)
(* (*   (* case hij: (i == j). *) *) *)
(* (*   (*   rewrite (eqP hij). *) *) *)
(* (*   (* rewrite size_proper_mul. *) *) *)
(* (*   (* move: (hs 0 0). *) *) *)
(* (*   (* rewrite eqxx => /eqP ->. *) *) *)
(* (*   (* move: (hs (lift 0 j) (lift 0 j)). *) *) *)
(* (*   (* rewrite eqxx => /eqP ->. *) *) *)
(* (*   (* rewrite addnS /=. *) *) *)
(* (*   (* move: (hs i j). *) *) *)
(* (*   (* done. *) *) *)
(* (*   admit. *) *)
(* (* (* exact: (key_invariant Hs i j). *) *) *)

(* (* have H2 : size (M' * r) <= (size a).*2.+1. *) *)
(* (*   rewrite (leq_trans (size_mul_leq M' r)) // -addnn. *) *)
(* (*   have := (leq_add Hm' Hr). *) *)
(* (*   rewrite !addSn addnS ltnS => HH. *) *)
(* (*   have H : (size M' + size r).-1 <= (size M' + size r). *) *)
(* (*     by case: (size M' + size r)%N. *) *)
(* (*   exact: (leq_trans H HH). *) *)

(* (* rewrite (test H1 H2). *) *)
(* (* case sa: (size a == 1)%N. *) *)
(* (*   by rewrite (eqP sa) prptnl0p -addnn mulrC. *) *)
(* (* rewrite -Hsize -prptnl_mul Hsize mulrC. *) *)
(* (* f_equal. *) *)
(* (* rewrite -addnn !addSn -!addnS prednK. *) *)
(* (*   rewrite prednK //. *) *)
(* (*   by case: (size a) an0. *) *)
(* (* by case: (size a) an0 sa => //= [[]]. *) *)
(* (* Qed.  *) *)


(* End poly_op. *)

(* (* Test computations *) *)

(* (* *)
(*    WARNING never use compute, but vm_compute, *)
(*    otherwise it's painfully slow *)
(* *) *)
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

(* (* Extraction Language Haskell. *) *)
(* (*  Extraction "Bareiss" ex_bdet. *) *)
