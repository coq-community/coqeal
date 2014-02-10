(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path ssralg.
Require Import fintype perm choice finfun matrix bigop zmodp poly mxpoly.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Open Scope ring_scope.

Section submatrix_def.

Variable A B : Type.

Definition submatrix T m n p q (f : 'I_p -> 'I_m) (g : 'I_q -> 'I_n) 
  (M : 'M[T]_(m,n)) := \matrix_(i < p, j < q) M (f i) (g j).

Lemma sub_submatrix k k' l l' m n (M : 'M[A]_(m,n)) (f' : 'I_k -> 'I_m) 
 (f : 'I_k' -> 'I_k) (g' : 'I_l -> 'I_n) (g : 'I_l' -> 'I_l) : 
  submatrix f g (submatrix f' g' M) = submatrix (f' \o f) (g' \o g) M.
Proof. by rewrite /submatrix; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma submatrix_map_mx (f : A -> B) m n p k (M : 'M[A]_(m,n))
  (g : 'I_p -> 'I_m) (h : 'I_k -> 'I_n) :
  submatrix g h (map_mx f M) = map_mx f (submatrix g h M).
Proof. by rewrite /submatrix; apply/matrixP=> i j; rewrite !mxE. Qed.

End submatrix_def.

Section lifting.

Lemma widen_ord_eq (m n : nat) (h h' : n <= m) : widen_ord h =1 widen_ord h'.
Proof. by move=> x; apply/ord_inj. Qed.

(* transform [a .. b] into [0, a+1, .., b+1] *)
Definition lift_pred m n (f : 'I_n -> 'I_m) : 'I_n.+1 -> 'I_m.+1 := 
  fun (x : 'I_(1 + n)) => 
    match split x with
      | inl _ => 0
      | inr j => lift 0 (f j)
    end.

Lemma size_tool n k : k <= n -> k < n.+1.
Proof. by rewrite ltnS. Qed.

(* lift step [ 0.. n-1] = [0 .. n ] *)
Lemma lift_pred_widen_ord m n (h : n <= m) :
  lift_pred (widen_ord h) =1 widen_ord (size_tool h).
Proof.
rewrite /lift_pred => x; have [y hx|y hx] := splitP; apply/ord_inj => //=.
by rewrite hx [y]ord1.
Qed.

Lemma lift_pred0 n k (f: 'I_k -> 'I_n) : lift_pred f 0 = 0.
Proof. by rewrite /lift_pred; case: splitP. Qed.

Lemma lift_predS n k (f : 'I_k -> 'I_n) (x : 'I_k) : 
  lift_pred f (lift 0 x) = lift 0 (f x).
Proof. by rewrite /lift_pred split1 liftK. Qed.

(* Lemma step0 n (h : 1 <= n.+1) (x : 'I_1) : widen_ord h x = 0. *)
(* Proof. by rewrite [x]ord1; apply/ord_inj. Qed. *)

(* Lemma stepn n (h : n <= n) (x : 'I_n) : widen_ord h x = x. *)
(* Proof. by apply/ord_inj. Qed. *)

Lemma inj_lift m n (f : 'I_n -> 'I_m) : injective f -> injective (lift_pred f).
Proof.
rewrite /lift_pred => hf x y; rewrite !split1.
have [/= j ->|->] := unliftP; last by have [|-> //] := unliftP.
by have [/= i -> /lift_inj/hf ->|] := unliftP.
Qed.

Lemma inj_widen_ord n m (h : n <= m) : injective (widen_ord h).
Proof.
move => x y hxy.
have /= {hxy} hxy : widen_ord h x = widen_ord h y :> nat by rewrite hxy.
by apply/ord_inj.
Qed.

End lifting.

Section submatrix_theory.

Variable R : ringType.

Lemma submatrix_eq m n p q (f1 g1 : 'I_p -> 'I_m) (f2 g2 : 'I_q -> 'I_n) 
  (M : 'M[R]_(m,n)) (h1 : f1 =1 g1) (h2 : f2 =1 g2) : 
  submatrix f1 f2 M = submatrix g1 g2 M.
Proof. by apply/matrixP => i j; rewrite !mxE (h1 i) (h2 j). Qed.

Lemma submatrix_lift_block m n p q (f1 : 'I_p -> 'I_m) (f2 : 'I_q -> 'I_n) 
  a (M: 'M[R]_(m,n)) (c : 'cV[R]_m) (l : 'rV[R]_n) : 
  submatrix (lift_pred f1) (lift_pred f2) (block_mx a%:M l c M) =
  block_mx a%:M (submatrix id f2 l) (submatrix f1 id c) (submatrix f1 f2 M).
Proof.
apply/matrixP => i j; rewrite !mxE /lift_pred !split1.
case: (oapp _ _ (unlift 0 i)) => x.
  rewrite unlift_none /= [x]ord1 !mxE !split1.
  case: (oapp _ _ (unlift 0 j)) => y; first by rewrite unlift_none [y]ord1.
  by rewrite liftK mxE.
rewrite liftK /= !mxE !split1.
case: (oapp _ _ (unlift 0 j)) => y; first by rewrite unlift_none mxE [y]ord1.
by rewrite liftK mxE.
Qed.

Lemma submatrix0 n m p q (f1 : 'I_p -> 'I_m) (f2 : 'I_q -> 'I_n) :
  submatrix f1 f2 0 = 0 :> 'M[R]__.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_scale m n p k (A : 'M[R]_(m,n)) 
  (f : 'I_p -> 'I_m) (g : 'I_k -> 'I_n) a :
  submatrix f g (a *: A) = a *: submatrix f g A.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_add m n p k (A B : 'M[R]_(m,n))
  (f : 'I_p -> 'I_m) (g : 'I_k -> 'I_n) :
  submatrix f g (A + B) = submatrix f g A + submatrix f g B.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_opp m n p k (A : 'M[R]_(m,n))
  (f : 'I_p -> 'I_m) (g : 'I_k -> 'I_n) :
  submatrix f g (- A) = - submatrix f g A.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_sub m n p k (A B : 'M[R]_(m,n))
  (f : 'I_p -> 'I_m) (g : 'I_k -> 'I_n) :
  submatrix f g (A - B) = submatrix f g A - submatrix f g B.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_mul m n p k l (A : 'M[R]_(m,n)) (B : 'M[R]_(n,p))
  (f : 'I_k -> 'I_m) (g : 'I_l -> 'I_p):
  submatrix f g (A *m B) = (submatrix f id A) *m (submatrix id g B).
Proof.
apply/matrixP => i j; rewrite !mxE.
by apply/eq_big => // x _; rewrite !mxE.
Qed.

Lemma submatrix_scalar_mx m p (f : 'I_p -> 'I_m) (hf : injective f) (a : R) :
  submatrix f f a%:M = a%:M.
Proof.
apply/matrixP => i j; rewrite !mxE.
case h : (f i == f j); first by rewrite (hf _ _ (eqP h)) eqxx.
by case h': (i == j) => //; move: h; rewrite (eqP h') eqxx.
Qed.

End submatrix_theory.

(* This must be put in a new section as it uses the theory on submatrix *)
Section submatrix_char_poly_mx.

Variable R : ringType.

Lemma submatrix_char_poly_mx m p (M : 'M[R]_m) 
  (f : 'I_p -> 'I_m) (hf : injective f) :
  submatrix f f (char_poly_mx M) = char_poly_mx (submatrix f f M).
Proof.
by rewrite /char_poly_mx -submatrix_map_mx submatrix_sub submatrix_scalar_mx.
Qed.

End submatrix_char_poly_mx.

(* Minors *)
Section minor_def.

Variable R : ringType.

Definition minor (m n p : nat) (f : 'I_p -> 'I_m) (g : 'I_p -> 'I_n) 
  (A : 'M[R]_(m,n)) := \det (submatrix f g A).

(* Principal minor *)
Definition pminor (m n p : nat) (h : p < m) (h' : p < n) (A : 'M[R]_(m,n)) := 
  minor (widen_ord h) (widen_ord h') A.

End minor_def.

Arguments minor {R m n p} f g A.

Section minor_theory.

Variable R : comRingType.

Lemma minor1 m n (A : 'M[R]_(m,n)) i j :
  minor (fun (_ : 'I_1) => i) (fun _ => j) A = A i j.
Proof. by rewrite /minor [submatrix _ _ _]mx11_scalar det_scalar1 !mxE. Qed.

Lemma minorn n (A : 'M[R]_n) : minor id id A = \det A.
Proof.
by rewrite /minor /submatrix; congr (\det _); apply/matrixP=> i j; rewrite mxE.
Qed.

Lemma det2 (A : 'M[R]_(2,2)) : \det A = A 0 0 * A 1 1 - A 1 0 * A 0 1.
Proof.
rewrite (expand_det_col _ 0) !big_ord_recl big_ord0 addr0 /cofactor /=.
rewrite ?(addn0,expr0,mul1r) /bump leq0n /= addn0 expr1.
do 2! rewrite [X in \det X]mx11_scalar det_scalar1 /=.
by rewrite !mxE !mulNr mul1r mulrN; do ?f_equal; apply/ord_inj.
Qed.

(* Sanity check of the definiton *)
Lemma minor2 m n (A : 'M[R]_(m,n)) (f : 'I_2 -> 'I_m) (g : 'I_2 -> 'I_n) : 
  minor f g A = A (f 0) (g 0) * A (f 1) (g 1) - A (f 1) (g 0) * A (f 0) (g 1).
Proof. by rewrite /minor det2 !mxE. Qed.

Lemma minor_ltn_eq0l k m1 m2 n1 n2 x (f : 'I_k -> 'I_(m1 + m2)) g 
  (M : 'M[R]_(m1,n1)) (N : 'M_(m1,n2)) (H : m1 < f x) : 
  minor f g (block_mx M N 0 0) = 0. 
Proof.
rewrite /minor (expand_det_row _ x) big1 // => i _; rewrite !mxE. 
case: splitP H => [j ->|j Hj]; first by rewrite ltnNge ltnW.
by rewrite row_mx0 mxE mul0r.
Qed.

Lemma minor_ltn_eq0r k m1 m2 n1 n2 x f (g : 'I_k -> 'I_(n1 + n2)) 
  (M : 'M[R]_(m1,n1)) (N : 'M_(m2,n1)) (H : n1 < g x) : 
  minor f g (block_mx M 0 N 0) = 0. 
Proof.
rewrite /minor (expand_det_col _ x) big1 // => i _; rewrite !mxE. 
by case: splitP=> j Hj; rewrite mxE; case: splitP H=> [l ->|l];
   rewrite ?ltnNge ?mxE ?mul0r // ltnW.
Qed.

Lemma minor_alternate_f m n p (f : 'I_p -> 'I_m) g (M : 'M[R]_(m,n)) : 
  (exists x y, (x != y) /\ (f x == f y)) -> minor f g M = 0.
Proof.
rewrite /minor => [[x [y [hxy /eqP hf]]]].
by rewrite (determinant_alternate hxy) // => a; rewrite !mxE hf.
Qed.

Lemma minor_alternate_g m n p (f : 'I_p -> 'I_m) g (M : 'M[R]_(m,n)) :
  (exists x y, (x != y) /\ (g x == g y)) -> minor f g M = 0.
Proof.
rewrite /minor => [[x [y [hxy /eqP hg]]]].
by rewrite -det_tr (determinant_alternate hxy) // => a /=; rewrite !mxE hg.
Qed.

Lemma minor_f_not_injective m n p (f : 'I_p -> 'I_m) g (M: 'M[R]_(m,n)) :
  ~ injective f -> minor f g M = 0.
Proof.
move/injectiveP/injectivePn => [x [y hxy hf]]; apply minor_alternate_f.
by exists x; exists y; rewrite hf.
Qed.

Lemma minor_g_not_injective m n p (f : 'I_p -> 'I_m) g (M: 'M[R]_(m,n)) :
  ~ injective g -> minor f g M = 0.
Proof.
move/injectiveP/injectivePn => [x [y hxy hg]]; apply minor_alternate_g.
by exists x; exists y; rewrite hg.
Qed.

Lemma minor_eq m n p (f1 g1 : 'I_p -> 'I_m) (f2 g2 : 'I_p -> 'I_n) 
  (h1 : f1 =1 g1) (h2 : f2 =1 g2) (M : 'M[R]_(m,n)) :
  minor f1 f2 M = minor g1 g2 M.
Proof. by rewrite /minor (submatrix_eq M h1 h2). Qed.

Lemma minor_lift_block m n p (f1 : 'I_p -> 'I_m) (f2 : 'I_p -> 'I_n) 
  a (M : 'M[R]_(m,n)) (l : 'rV[R]_n) : 
  minor (lift_pred f1) (lift_pred f2) (block_mx a%:M l 0 M) = a * minor f1 f2 M.
Proof.
by rewrite /minor submatrix_lift_block submatrix0 (@det_ublock _ 1) det_scalar1.
Qed.

End minor_theory. 

Section minor_char_poly_mx.

Variable R : comRingType.

(* all principal minor of the characteristic matrix are monic *)
Lemma pminor_char_poly_mx_monic m p (M : 'M[R]_m) (h h': p.+1 <= m) :
  pminor h h' (char_poly_mx M) \is monic.
Proof.
have h'h : widen_ord h' =1 widen_ord h by apply/widen_ord_eq.
rewrite /pminor (minor_eq (frefl _) h'h) /minor submatrix_char_poly_mx.
  by rewrite char_poly_monic.
exact: inj_widen_ord.
Qed.

End minor_char_poly_mx.