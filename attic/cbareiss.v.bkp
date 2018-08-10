(* Executable version *)

Require Import cssralg cdvdring Matrix cseqpoly cseqpolydvd.

Import CSeqPoly_dvd.

Section exBareiss.

Variable R : dvdRingType.
Variable CR: cdvdRingType R.

Fixpoint exBareiss_rec n g (M: Matrix CR) := match n,M with
  | _,eM => g
  | O,_ => g
  | S p, cM a l c M =>
    let M' := subM (multEM a M) (mults c l) in
    let M'' := divM g (zero CR) M' in
      exBareiss_rec p a M''
end.

Lemma exBareiss_rec_unfold : forall n g a l c M,
  exBareiss_rec (1 + n) g (cM a l c M) =
    exBareiss_rec n a (divM g (zero CR) (subM (multEM a M) (mults c l))).
Proof. by []. Qed.

Lemma exBareiss_recE : forall n (g: R) (M: 'M[R]_(1 + n)),
  trans (Bareiss_rec g M) =
    exBareiss_rec (1+n) (trans g) (trans M).
Proof.
elim => [ /= g M | n hi g]  //.
- by rewrite [dlsubmx M]flatmx0 [ursubmx M]thinmx0 cV2seq0 rV2seq0 /=.
rewrite [n.+1]/(1 + n)%nat  => M.
rewrite -{2}[M]submxK [ulsubmx M]mx11_scalar !mxE lshift0
        block_mxE exBareiss_rec_unfold.
by rewrite [Bareiss_rec _ _]/= hi divME zeroE subE multEME multsE.
Qed.

Definition exBareiss n (M : Matrix CR) := exBareiss_rec n (one CR) M.

Lemma exBareissE : forall n (M : 'M[R]_(1 + n)),
  trans (Bareiss M) = exBareiss (1 + n) (mat2Matrix _ M).
Proof.
rewrite /Bareiss /exBareiss => n M.
by rewrite exBareiss_recE oneE.
Qed.

Definition ex_char_poly_mx n (M : Matrix CR) :=
  subM (multEM (indet _ 1) (ident _ n)) (mapM (@polyC_seq _ _) M).

Lemma ex_char_poly_mxE : forall n (M : 'M[R]_n),
  trans (char_poly_mx M) = ex_char_poly_mx n (trans M).
Proof.
rewrite /ex_char_poly_mx /char_poly_mx => n M.
rewrite subE -scalemx1 multEME idmxE -indetE expr1
  (@map_mxE _ _ _ _ _  (@polyC_seq R CR)) // => a.
by rewrite -polyC_seqE.
Qed.

End exBareiss.

Section exDet.

Variable R : dvdRingType.
Variable CR: cdvdRingType R.

Definition ex_char_poly_alt (n : nat) (M : Matrix CR) :=
  exBareiss n (ex_char_poly_mx n M).

Lemma ex_char_polyE : forall n (M : 'M[R]_(1 + n)),
  trans (char_poly_alt M) = ex_char_poly_alt (1 + n) (mat2Matrix CR M).
Proof.
rewrite /char_poly_alt /ex_char_poly_alt => n M.
by rewrite -ex_char_poly_mxE -exBareissE.
Qed.

Definition ex_bdet (n : nat) (M : Matrix CR) :=
  nth (zero CR) (ex_char_poly_alt n (oppM M)) 0.

Lemma ex_detE : forall n (M : 'M[R]_(1 + n)),
  trans (bdet M) = ex_bdet (1 + n) (mat2Matrix CR M).
Proof.
rewrite /ex_bdet /bdet => n M.
rewrite -oppME -ex_char_polyE -[zero CR]zeroE.
by case: char_poly_alt => [[]].
Qed.

End exDet.

(* Executable version *)

Require Import cssralg Matrix cseqpoly.

Section exBareiss.

Variable R : comRingType.
Variable CR: cringType R.

Definition cpoly := seq_cringType CR.

Definition ex_dvd_step d (M : Matrix cpoly) :=
 mapM (fun x => divp_seq x d) M.

Lemma ex_dvd_stepE (m n: nat) (d: {poly R}) (M: 'M[{poly R}]_(m,n)):
 trans (dvd_step d M) = ex_dvd_step (trans d) (trans M).
Proof.
rewrite /dvd_step /ex_dvd_step.
case : m n M => [ | m] [ | n].
  by move=> M; rewrite [M]thinmx0.
  by move=> M; rewrite [M]flatmx0.
  by move=> M; rewrite [M]thinmx0.
rewrite [m.+1]/(1 + m)%N [n.+1]/(1 + n)%N => M.
rewrite -[M]submxK /trans /= !mxE -map_ursubmx -map_dlsubmx -map_drsubmx
   block_mxKur block_mxKdl !block_mxKdr.
case: splitP => x // _; rewrite [x]ord1 !mxE; clear x.
case: splitP => x // _; rewrite [x]ord1 !mxE !lshift0; clear x.
set f := fun x => divp_seq x (trans d).
set g := fun x => rdivp x d.
have h : forall a, trans (g a) = f (trans a)
  by rewrite /f /g => a; rewrite -divp_seqE.
by rewrite -divp_seqE (rV2seq_map h) (cV2seq_map h) (mat2Matrix_map h).
Qed.

Fixpoint exBareiss_rec n g (M: Matrix cpoly) := match n,M with
  | _,eM => g
  | O,_ => g
  | S p, cM a l c M =>
    let M' := subM (multEM a M) (mults c l) in
    let M'' := ex_dvd_step g M' in
      exBareiss_rec p a M''
end.

Lemma exBareiss_rec_unfold : forall n g a l c M,
  exBareiss_rec (1 + n) g (cM a l c M) =
    exBareiss_rec n a (ex_dvd_step g (subM (multEM a M) (mults c l))).
Proof. by []. Qed.

Lemma exBareiss_recE : forall n (g: {poly R}) (M: 'M[{poly R}]_(1 + n)),
  trans (Bareiss_rec g M) =
    exBareiss_rec (1+n) (trans g) (trans M).
Proof.
elim => [ /= g M | n hi g]  //.
- by rewrite [dlsubmx M]flatmx0 [ursubmx M]thinmx0 cV2seq0 rV2seq0 /=.
rewrite [n.+1]/(1 + n)%nat  => M.
rewrite -{2}[M]submxK [ulsubmx M]mx11_scalar !mxE lshift0
        block_mxE exBareiss_rec_unfold.
rewrite [Bareiss_rec _ _]/= hi.
rewrite (@map_mxE _ _ _ _ _ (fun x : seq CR => divp_seq x (trans g)))
 ?subE ?multEME ?multsE // => a.
by rewrite -divp_seqE.
Qed.

Notation "'1'" := (one cpoly).

Definition exBareiss n (M: Matrix cpoly) := exBareiss_rec n 1 M.

Lemma exBareissE : forall n (M: 'M[{poly R}]_(1 + n)),
  trans (Bareiss M) = exBareiss (1 + n) (trans M).
Proof.
rewrite /Bareiss /exBareiss => n M.
by rewrite exBareiss_recE oneE.
Qed.

Notation "'\X'" := (indet _ 1).

Definition ex_char_poly_mx n (M : Matrix CR) :=
 subM (multEM \X (ident _ n)) (mapM (@polyC_seq _ CR) M).

Lemma ex_char_poly_mxE : forall n (M: 'M[R]_n),
  trans (char_poly_mx M) = ex_char_poly_mx n (trans M).
Proof.
rewrite /ex_char_poly_mx /char_poly_mx => n M.
rewrite subE -scalemx1 multEME idmxE -indetE expr1
  (@map_mxE _ _ _ _ _  (@polyC_seq R CR)) // => a.
by rewrite -polyC_seqE.
Qed.

End exBareiss.

Section exDet.

Variable R : comRingType.
Variable CR: cringType R.

Definition ex_char_poly_alt n (M : Matrix CR) :=
  exBareiss n (ex_char_poly_mx n M).

Lemma ex_char_polyE : forall n (M: 'M[R]_(1 + n)),
  trans (char_poly_alt M) = ex_char_poly_alt (1 + n) (trans M).
Proof.
rewrite /char_poly_alt /ex_char_poly_alt => n M.
by rewrite -ex_char_poly_mxE -exBareissE.
Qed.

Definition ex_bdet n (M : Matrix CR) :=
  nth (zero CR) (ex_char_poly_alt n (oppM M)) 0.

Lemma ex_detE : forall n (M : 'M[R]_(1 + n)),
  trans (bdet M) = ex_bdet (1 + n) (trans M).
Proof.
rewrite /ex_bdet /bdet => n M.
rewrite -oppME -ex_char_polyE -[zero CR]zeroE.
by case: char_poly_alt => [[]].
Qed.

End exDet.

(* Extraction Language Haskell. *)
(*  Extraction "Bareiss" ex_bdet. *)
