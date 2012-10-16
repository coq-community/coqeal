Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice finfun.
Require Import matrix  bigop zmodp mxalgebra poly mxpoly.
Require Import ssrcomplements.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Open Scope ring_scope.

Section submatrix_section.
Variable T : Type.

Definition submatrix m n p q 
 (f : 'I_p -> 'I_m) (g : 'I_q -> 'I_n) (A: 'M[T]_(m,n)):= 
    \matrix_(i < p, j < q) A (f i) (g j).

Lemma sub_submx k k' l l' m n (A : 'M[T]_(m,n)) (f' : 'I_k -> 'I_m) 
 (f : 'I_k' -> 'I_k) (g' : 'I_l -> 'I_n) (g : 'I_l' -> 'I_l) : 
  submatrix f g (submatrix f' g' A) = submatrix (f' \o f) (g' \o g) A.
Proof.
by rewrite /submatrix -matrix_comp.
Qed.

End submatrix_section.

Section minor_def.
Variable R : ringType.

Definition minor (m n k: nat) (f1 : 'I_k -> 'I_m) (f2: 'I_k -> 'I_n)
 (A: 'M[R]_(m,n)) := \det (submatrix f1 f2 A).

End minor_def.

(* Notation "[ '\minor_' k 'of' A 'using' f & g ]" := 
  (\det (@submatrix _ _ _ k k f g A))
   (at level 0, f at level 99,
    format "[ '\minor_' k  'of'  A  'using'  f  &  g ]") : form_scope. *)


Section minor_section.
Variable R : comRingType.
 
Lemma minor1 : forall (m n: nat) (A: 'M[R]_(m,n)) i j,
 minor (fun _ : 'I_1 => i) (fun _ => j) A = A i j.
Proof.
move => m n A i j.
by rewrite /minor [submatrix _ _ _]mx11_scalar det_scalar1 !mxE.
Qed.

(* subset [0 .. k-1] of [0 .. n-1] *)
Definition step_fun (n k:nat) (h : k <= n) : 'I_k -> 'I_n :=
  fun x => widen_ord h x.

Lemma step_fun_eq (n k : nat) (h h' : k <= n) : step_fun h =1 step_fun h'.
Proof.
rewrite /step_fun => x.
by apply/ord_inj.
Qed.

(* transform [a .. b] into [0, a+1, .., b+1] *)
Definition lift_pred (n k:nat) (f: 'I_k -> 'I_n)
  : 'I_k.+1 -> 'I_n.+1 :=
fun (x: 'I_(1 + k)) => match split x with
           | inl _ => 0
           | inr j => lift 0 (f j)
         end.

(* Principal minor *)
Definition pminor (m n k:nat) (h: k.+1 <= m) (h': k.+1 <= n)
  (A: 'M[R]_(m,n)) := minor (step_fun h) (step_fun h') A.

Lemma size_tool : forall n k, k <= n -> k.+1 <= n.+1.
Proof.
move => n k h.
by rewrite ltnS.
Qed.

(* lift step [ 0.. k-1] = [0 .. k ] *)
Lemma lift_pred_step : forall (n k:nat) (h : k <= n) (x: 'I_k.+1),
  lift_pred (step_fun h) x = step_fun (size_tool h) x.
Proof.
rewrite /lift_pred /step_fun => n k h x.
case: splitP => y.
- rewrite [y]ord1 /= => hx.
  have -> /= : x = 0 by apply/ord_inj.
  by apply/ord_inj.
move => hx.
have -> /= : x = lift 0 y by apply/ord_inj.
by apply/ord_inj.
Qed.

Lemma step0 : forall n (h: 1 <= n.+1) (x: 'I_1),
  step_fun h x = 0.
Proof.
rewrite /step_fun => n  h x /=.
rewrite [x]ord1; by apply/ord_inj.
Qed.

Lemma stepn: forall n (x: 'I_n) (h: n <= n),
  step_fun h x = x.
Proof.
rewrite /step_fun => n x h.
by apply/ord_inj.
Qed.

Lemma minorn : forall (n:nat) (A: 'M[R]_n),
  @minor _ _ _ n id id A = \det A.
Proof.
rewrite /minor /submatrix => n A.
f_equal.
by apply/matrixP => i j; rewrite !mxE.
Qed.

Lemma det2 : forall (A: 'M[R]_(2,2)),
  \det A = A 0 0 * A 1 1 - A 1 0 * A 0 1.
Proof.
move => A.
rewrite (expand_det_col _ 0) !big_ord_recl big_ord0 addr0.
rewrite /cofactor /= !addn0 !expr0 !mul1r /bump leq0n /= addn0 expr1.
do 2! rewrite [X in \det X]mx11_scalar det_scalar1 /=.
rewrite !mxE !mulNr mul1r mulrN.
by repeat f_equal; apply/ord_inj.
Qed.

Lemma minor2 : forall (m n:nat) (A: 'M[R]_(m,n))
  (f1 : 'I_2 -> 'I_m) f2,
  minor f1 f2 A =
    A (f1 0) (f2 0) * A (f1 1) (f2 1) -
    A (f1 1) (f2 0) * A (f1 0) (f2 1).
Proof.
rewrite /minor /submatrix => m n A f1 f2.
by rewrite det2 !mxE.
Qed.

End minor_section.

Section Theory.
Variable R: comRingType.

Lemma minor_alternate_f : forall (m n p:nat) 
  (f : 'I_p -> 'I_m) g (M: 'M[R]_(m,n)),
  (exists x, exists y, (x != y) /\ (f x == f y)) -> minor f g M = 0.
Proof.
rewrite /minor => m n p f g M [x [y [hxy hf]]].
apply: (determinant_alternate hxy) => a /=.
by rewrite !mxE (eqP hf).
Qed.

Lemma minor_alternate_g : forall (m n p:nat) 
   (f : 'I_p -> 'I_m) g (M: 'M[R]_(m,n)),
  (exists x, exists y, (x != y) /\ (g x == g y)) -> minor f g M = 0.
Proof.
rewrite /minor => m n p f g M [x [y [hxy hg]]].
rewrite -det_tr.
apply: (determinant_alternate hxy) => a /=.
by rewrite !mxE (eqP hg).
Qed.

Lemma minor_f_not_injective : forall (m n p:nat) 
   (f : 'I_p -> 'I_m) g (M: 'M[R]_(m,n)),
   ~ injective f -> minor f g M = 0.
Proof.
move => m n p f g M /injectiveP /injectivePn [x [y hxy hf]].
apply minor_alternate_f.
by exists x; exists y; split => //; rewrite hf.
Qed.

Lemma minor_g_not_injective : forall (m n p:nat) 
  (f : 'I_p -> 'I_m) g (M: 'M[R]_(m,n)),
   ~ injective g -> minor f g M = 0.
Proof.
move => m n p f g M /injectiveP /injectivePn [x [y hxy hg]].
apply minor_alternate_g.
by exists x; exists y; split => //; rewrite hg.
Qed.

Lemma submatrix_eq : forall (m n p q :nat) (f1 f1': 'I_p -> 'I_m)
  (f2 f2' : 'I_q -> 'I_n) (M: 'M[R]_(m,n)),
    f1 =1 f1'-> f2 =1 f2' ->
 submatrix f1 f2 M = submatrix f1' f2' M.
Proof.
rewrite /submatrix => m n p q f1 f1' f2 f2' M h1 h2.
by apply/matrixP => i j; rewrite !mxE (h1 i) (h2 j).
Qed.

Lemma minor_eq : forall (m n k:nat) 
  (f1 : 'I_k -> 'I_m) g1 f2 g2 (M: 'M[R]_(m,n)),
  (f1 =1 g1) -> (f2 =1 g2) -> minor f1 f2 M = minor g1 g2 M.
Proof.
rewrite /minor => m n k f1 g1 f2 g2 M h1 h2.
by rewrite (submatrix_eq M h1 h2).
Qed.

Lemma lift_pred0 : forall n k (f: 'I_k -> 'I_n),
  lift_pred f 0 = 0.
Proof.
rewrite /lift_pred => n k f.
by case: splitP.
Qed.

Lemma lift_predS : forall n k (f: 'I_k -> 'I_n) (x: 'I_k),
  lift_pred f (lift 0 x) = lift 0 (f x).
Proof.
rewrite /lift_pred => n k f x.
case: splitP => y /= ; first by rewrite [y]ord1.
move/eqP; rewrite eqSS => /eqP h.
by have -> : x = y by apply/ord_inj.
Qed.

Lemma submatrix_lift_block : forall (m n p q:nat)
  (f1 : 'I_p -> 'I_m) (f2 : 'I_q -> 'I_n) a
  (M: 'M[R]_(m,n)) (c: 'cV[R]_m) (l: 'rV[R]_n),
  submatrix (lift_pred f1) (lift_pred f2)
    (block_mx a%:M l c M) =
  block_mx a%:M (submatrix id f2 l) (submatrix f1 id c)
    (submatrix f1 f2 M).
Proof.
rewrite /submatrix => m n p q f1 f2 a M c l.
symmetry; apply/matrixP => i j; rewrite !mxE.
case: splitP => x /=.
- rewrite [x]ord1 !mxE => hi {x}.
  have -> : i = 0 by apply/ord_inj.
  rewrite lift_pred0 {i hi}.
  symmetry.
  case: splitP => z // _; rewrite [z]ord1 !mxE {z}.
  symmetry.
  case: splitP => y /=.
  + rewrite [y]ord1 !mxE => hj {y}.
    have -> : j = 0 by apply/ord_inj.
    rewrite lift_pred0 {j hj}.
    by case: splitP => z // _; rewrite [z]ord1 !mxE {z}.
  rewrite !mxE => hj.
  have -> : j = lift 0 y by apply/ord_inj.
  rewrite lift_predS {j hj}.
  case: splitP => z /=; first by rewrite [z]ord1.
  move/eqP; rewrite eqSS => /eqP h.
  by have -> : f2 y = z by apply/ord_inj.
rewrite !mxE => hi.
have -> : i = lift 0 x by apply/ord_inj.
rewrite lift_predS {i hi}.
case: splitP => y /=.
- rewrite [y]ord1 !mxE => hj.
  have -> : j = 0 by apply/ord_inj.
  case: splitP => z /=; first by rewrite [z]ord1.
  move/eqP; rewrite eqSS !mxE => /eqP h.
  rewrite lift_pred0.
  case: splitP => w //= _; rewrite [w]ord1.
  by have -> : f1 x = z by apply/ord_inj.
rewrite !mxE => hj.
have -> : j = lift 0 y by apply/ord_inj.
case: splitP => z /=; first by rewrite [z]ord1.
move/eqP; rewrite eqSS !mxE => /eqP h.
rewrite lift_predS.
case: splitP => w /=; first by rewrite [w]ord1.
move/eqP; rewrite eqSS => /eqP h'.
have -> : f1 x = z by apply/ord_inj.
by have -> : f2 y = w by apply/ord_inj.
Qed.

Lemma submatrix0 : forall n m p q (f1: 'I_p -> 'I_m) (f2 : 'I_q -> 'I_n),
  submatrix f1 f2 0 = 0 :> 'M[R]_(_,_).
Proof.
by move => n m p q f1 f2; apply/matrixP => i j; rewrite !mxE.
Qed.

Lemma minor_lift_block : forall (m n p :nat)
  (f1 : 'I_p -> 'I_m) f2 a (M: 'M[R]_(m,n)) (l: 'rV[R]_n),
  minor (lift_pred f1) (lift_pred f2) (block_mx a%:M l 0 M) =
  a * minor f1 f2 M.
Proof.
rewrite /minor => m n p f1 f2 a M l.
rewrite submatrix_lift_block submatrix0.
by rewrite (@det_ublock _ 1) det_scalar1.
Qed.

Lemma inj_lift : forall m n (f: 'I_n -> 'I_m),
  injective f -> injective (lift_pred f).
Proof.
rewrite /lift_pred => m n f hf x y.
case: splitP => [ z | z hx].
- rewrite [z]ord1 => hz {z}.
  have -> : x = 0 by apply/ord_inj.
  case: splitP => w //.
  rewrite [w]ord1 => hw {w}.
  by have -> : y = 0 by apply/ord_inj.
have -> : x = lift 0 z by apply/ord_inj.
case: splitP => w // hy.
have -> : y = lift 0 w by apply/ord_inj.
by move/lift_inj/hf ->.
Qed.

Lemma inj_step : forall n m (h: n <= m),
  injective (step_fun h).
Proof.
rewrite /step_fun => n m h x y hxy.
apply/ord_inj.
by have /= : widen_ord h x = widen_ord h y :> nat by rewrite hxy.
Qed.

Lemma submatrix_scale m n p k (A: 'M[R]_(m,n))
  (f : 'I_p -> 'I_m) (g : 'I_k -> 'I_n) a:
  submatrix f g (a *: A) = a *: submatrix f g A.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_add m n p k (A B : 'M[R]_(m,n))
  (f : 'I_p -> 'I_m) (g : 'I_k -> 'I_n):
  submatrix f g (A + B) = submatrix f g A + submatrix f g B.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_opp m n p k (A: 'M[R]_(m,n))
  (f : 'I_p -> 'I_m) (g : 'I_k -> 'I_n) :
  submatrix f g (- A ) = - submatrix f g A.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma submatrix_mul m n p k l (A: 'M[R]_(m,n)) (B: 'M[R]_(n,p))
  (f : 'I_k -> 'I_m) (g : 'I_l -> 'I_p):
  submatrix f g (A *m B) = (submatrix f id A) *m (submatrix id g B).
Proof.
apply/matrixP => i j; rewrite !mxE.
by apply/eq_big => // x _; rewrite !mxE /=.
Qed.

Lemma submatrix_char_poly_mx : forall m p(M: 'M[R]_m)
  (f1: 'I_p -> 'I_m), injective f1 ->
  submatrix f1 f1 (char_poly_mx M) = char_poly_mx (submatrix f1 f1 M).
Proof.
rewrite /submatrix /char_poly_mx => m p M f1 hf.
apply/matrixP => i j; rewrite !mxE.
case h : (f1 i == f1 j).
- by rewrite (hf _ _ (eqP h)) eqxx.
case h': (i == j) => //.
by move: h; rewrite (eqP h') eqxx.
Qed.

End Theory.