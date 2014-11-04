Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice fingroup.
Require Import matrix bigop zmodp mxalgebra poly.

Require Import ssrcomplements dvdring.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** Strongly discrete rings *)
Module StronglyDiscrete.

CoInductive member_spec (R : ringType) n (x : R) (I : 'rV[R]_n)
  : option 'cV[R]_n -> Type :=
| Member J of x%:M = I *m J : member_spec x I (Some J)
| NMember of (forall J, x%:M != I *m J) : member_spec x I None.

Record mixin_of (R : ringType) : Type := Mixin {
  member : forall n, R -> 'rV_n -> option 'cV_n;
  _ : forall n (x : R) (I : 'rV_n), member_spec x I (member x I)
}.

Section ClassDef.

(* (* In the future we should base it on commutative rings *)
Record class_of (R : Type) : Type := Class {
  base  : GRing.ComRing.class_of R;
  mixin : mixin_of (GRing.ComRing.Pack base R)
}.

Local Coercion base : class_of >-> GRing.ComRing.class_of.
*)

Record class_of (R : Type) : Type := Class {
  base  : GRing.IntegralDomain.class_of R;
  mixin : mixin_of (GRing.IntegralDomain.Pack base R)
}.
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

(* Definition pack b0 (m0 : mixin_of (@GRing.ComRing.Pack T b0 T)) := *)
(*   fun bT b & phant_id (GRing.ComRing.class bT) b => *)
(*   fun    m & phant_id m m0 => Pack (@Class T b m) T. *)

Definition pack b0 (m0 : mixin_of (@GRing.IntegralDomain.Pack T b0 T)) :=
  fun bT b & phant_id (GRing.IntegralDomain.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.

End ClassDef.

Module Exports.
(* Coercion base : class_of >-> GRing.ComRing.class_of. *)
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Notation stronglyDiscreteType := type.
Notation StronglyDiscreteType T m := (@pack T _ m _ _ id _ id).
Notation StronglyDiscreteMixin := Mixin.
Notation "[ 'stronglyDiscreteType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'stronglyDiscreteType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'stronglyDiscreteType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'stronglyDiscreteType'  'of'  T ]") : form_scope.
End Exports.

End StronglyDiscrete.
Export StronglyDiscrete.Exports.

Definition member R := StronglyDiscrete.member (StronglyDiscrete.class R).
Definition member_spec := StronglyDiscrete.member_spec.

Delimit Scope ideal_scope with IS.

Section StronglyDiscreteTheory.

Variable R : stronglyDiscreteType.

Implicit Types a b c : R.

Lemma member_specP : forall n (x : R) (I : 'rV[R]_n),
  member_spec x I (member x I).
Proof. by case: R => [? [? []]]. Qed.

Lemma memberP n (x : R) (I : 'rV[R]_n) :
  reflect (exists J, I *m J = x%:M) (member x I).
Proof.
case: member_specP=> /= [J ->|h]; first by apply: ReflectT; exists J.
apply: ReflectF=> [[J hJ]].
by move: (h J); rewrite hJ eqxx.
Qed.

Lemma member0 n (I : 'rV[R]_n) : member 0 I.
Proof.
case: member_specP => //= /(_ 0).
rewrite mulmx0. 
have -> : 0%:M = 0 by move=> *; apply/matrixP => i j; rewrite !mxE mul0rn.
by rewrite eqxx.
Qed.

(** If x is one of the generators then x is in I *)
Lemma member_in m x (I : 'rV[R]_m) : (exists i, I 0 i = x) -> member x I.
Proof.
case=> y Hy; apply/memberP.
exists (delta_mx y 0).
have -> : I *m delta_mx y 0 = (delta_mx 0 y *m I^T)^T
  by move=> n; rewrite trmx_mul trmxK trmx_delta.
rewrite -rowE tr_row trmxK -Hy.
by apply/rowP=> i; rewrite !mxE ord1 eqxx mulr1n.
Qed.

(** Ideal theory of strongly discrete rings *)
Section IdealTheory.

(** The sub-ideal membership function *)
Fixpoint subid m n : 'rV[R]_m -> 'rV[R]_n -> bool :=
  match m return 'rV[R]_m -> 'rV[R]_n -> bool with
    | S p => fun (I : 'rV[R]_(1 + _)) J =>
          member (I 0 0) J && subid (rsubmx I) J
    | _ => fun _ _ => true
  end.

Arguments Scope subid
  [nat_scope nat_scope ideal_scope ideal_scope].
Prenex Implicits subid.
Local Notation "A <= B" := (subid A B) : ideal_scope.
Local Notation "A <= B <= C" := ((A <= B) && (B <= C))%IS : ideal_scope.
Local Notation "A == B" := (A <= B <= A)%IS : ideal_scope.

Lemma subidP : forall m n (I : 'rV[R]_m) (J : 'rV[R]_n),
  reflect (exists D, I = J *m D) (I <= J)%IS.
Proof.
elim=> [m I J|n ih m].
  by rewrite thinmx0; apply: ReflectT; exists 0; rewrite mulmx0.
rewrite [n.+1]/(1 + n)%N=> I J.
rewrite -[I]hsubmxK /= row_mxKr.
have -> : ((row_mx (lsubmx I) (rsubmx I)) 0 0) = I 0 0
  by rewrite !mxE; case: splitP => i //=; rewrite !ord1 !mxE lshift0.
have -> : lsubmx I = (I 0 0)%:M
  by apply/matrixP=> i j; rewrite !ord1 !mxE lshift0 eqxx mulr1n.
case: member_specP => [J' hJ'|h].
  apply: (iffP idP) => [/ih [X hX]|[]].
    exists (row_mx J' X).
    by rewrite (@mul_mx_row _ _ _ 1) -hJ' -hX.
  rewrite [n.+1]/(1 + n)%N => x.
  rewrite -[x]hsubmxK (@mul_mx_row _ _ _ 1) => /eq_row_mx [h1 h2].
  by apply/ih; exists (rsubmx x).
apply: ReflectF => [[]].
rewrite [n.+1]/(1 + n)%N => X.
rewrite -[X]hsubmxK (@mul_mx_row _ _ _ 1) => /eq_row_mx [h1 h2].
by case/eqP: (h (lsubmx X)).
Qed.

Lemma member_subidP m (I: 'rV[R]_m) (a: R) :
  reflect (member a I) (a%:M <= I)%IS.
Proof.
apply/(iffP idP).
  by case/subidP => C hC; apply/memberP; exists C.
by case/memberP => C hC; apply/subidP; exists C.
Qed.

Lemma member_subid m n x (I: 'rV[R]_m) (J: 'rV[R]_n) :
  member x I -> (I <= J)%IS -> member x J.
Proof.
case/memberP => C hC.
case/subidP => D hD.
apply/memberP; exists (D *m C).
by rewrite -hC hD mulmxA.
Qed.

Lemma subid_memberP m n (I: 'rV[R]_m) (J: 'rV[R]_n) :
  reflect (forall x, member x I -> member x J) (I <= J)%IS.
Proof.
apply: (iffP idP) => /= [|h1].
- case/subidP => C hC x /memberP [D hD]; apply/memberP.
  by exists (C *m D); rewrite mulmxA -hC.
elim: m n I J h1 => //= m ih n.
rewrite [m.+1]/(1 + m)%N => I J hIJ; rewrite hIJ /=.
  apply/ih => x hx; apply/hIJ/memberP.
  case/memberP: hx => [D hD].
  exists (col_mx (0 : 'M[R]_1) D).
  by rewrite -[I]hsubmxK (@mul_row_col _ _ 1) mulmx0 add0r hD.
apply/memberP.
exists (col_mx (1 : 'M[R]_1) 0).
rewrite -[I]hsubmxK (@mul_row_col _ _ 1) mulmx1 mulmx0 addr0.
apply/rowP=> i.
rewrite ord1 !mxE lshift0.
case: splitP => //= j _.
by rewrite ord1 !mxE lshift0.
Qed.

(** If the generators of I are generators of J then I <= J *)
Lemma subid_in : forall m n (I : 'rV[R]_m) (J : 'rV[R]_n),
  (forall i, exists j, J 0 j = I 0 i) -> (I <= J)%IS.
Proof.
elim => //= m ih n.
rewrite [m.+1]/(1 + m)%N => I J h.
rewrite ih /= ?andbT => [|i].
  by apply/member_in; case: (h 0)=> x hx; exists x.
by rewrite mxE; apply: (h (rshift 1 i)).
Qed.

(** A function that explicitly computes the witness. This is useful for
   coherent rings *)
Fixpoint subidW m n : 'rV[R]_m -> 'rV[R]_n -> 'M[R]_(n,m) :=
  match m return 'rV[R]_m -> 'rV[R]_n -> 'M[R]_(n,m) with
    | S p => fun (I : 'rV[R]_(1 + _)) J => match member (I 0 0) J with
      | Some w => row_mx w (subidW (rsubmx I) J)
      | None   => 0
      end
    | _ => fun _ _ => 0
  end.

Lemma subidWP m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  reflect (I = J *m subidW I J) (I <= J)%IS.
Proof.
elim: m n I J => [m I J|n ih m].
  by rewrite thinmx0 mulmx0; apply: ReflectT.
rewrite [n.+1]/(1 + n)%N=> I J.
rewrite -[I]hsubmxK /= row_mxKr.
have -> : ((row_mx (lsubmx I) (rsubmx I)) 0 0) = I 0 0
  by rewrite !mxE; case: splitP => i //=; rewrite !ord1 !mxE lshift0.
have -> : lsubmx I = (I 0 0)%:M
  by apply/matrixP=> i j; rewrite !ord1 !mxE lshift0 eqxx mulr1n.
case: member_specP => [J' hJ'|/(_ 0)] /=.
  apply: (iffP idP) => [/ih|].
    by rewrite (@mul_mx_row _ _ _ 1) hJ' => <-.
  rewrite hJ' (@mul_mx_row _ _ _ 1) => /(@eq_row_mx _ _ 1) [h1 h2].
  by apply/ih.
rewrite !mulmx0 => h.
apply: ReflectF; apply/eqP; move: h; apply: contra.
have -> : (0 : 'rV[R]_(1 + n)%N)= row_mx (0 : 'rV[R]_1) 0 by rewrite row_mx0.
by case/eqP/(@eq_row_mx _ _ 1) => ->.
Qed.

(* (* This was useful at some point for building a witness *)
Fixpoint build_mem m n (J: 'rV[R]_n) {struct m} :=
  match m return 'rV[R]_m -> option 'M[R]_(n,m) with
    | S p => fun (I: 'rV[R]_(1 + p)) =>
           match build_mem _ J (rsubmx I), member (I 0 0) J with
              | Some tl, Some hd => Some (row_mx hd tl)
              | _,_ => None
           end
    | O  => fun _ => Some 0
  end.

(* could use CoInductive but lazy *)
Lemma build_memP : forall m n (I: 'rV[R]_m) (J: 'rV[R]_n),
  (forall x, member x I -> member x J) ->
  match build_mem J I with
    | Some D => I = J*m D
    | None   => False
  end.
Proof.
elim => [ | m hi] n //=.
- by move => I J _; rewrite thinmx0 mulmx0.
rewrite [m.+1]/(1 + m)%N => I J hI.
have h : forall x, member x (rsubmx I) -> member x J.
- move => /= x /memberP [C hC]; apply: hI.
  apply/memberP; exists (col_mx (0: 'M_1) C).
  by rewrite -[I]hsubmxK (@mul_row_col _ 1 1) mulmx0 hC add0r.
move: (hi n (rsubmx I) J h).
case: build_mem => [ rest hrest | ] //.
case: member_specP => /= [D hD | hD]; last first.
- have : member (I 0 0) J by apply/hI/member_in; exists 0.
  case/memberP => C hC.
  by move: (hD C); rewrite -hC eqxx.
rewrite (@mul_mx_row _ _ _ 1) -hrest -hD -{1}[I]hsubmxK; f_equal.
by apply/rowP => i; rewrite !mxE !ord1 lshift0.
Qed.
*)


(** Theory of subid and eqid *)

Lemma sub0id m n (I : 'rV[R]_m) : ((0 : 'rV[R]_n) <= I)%IS.
Proof. by apply/subidP; exists 0; rewrite mulmx0. Qed.

Lemma subid_eq0 m n (I : 'rV[R]_n) :
  (I <= (0 : 'rV[R]_m))%IS = (I == 0).
Proof.
apply/subidP/eqP => [[D -> ]|->]; first by rewrite mul0mx.
by exists 0; rewrite mul0mx.
Qed.

Lemma eqid_eq0 m n (I : 'rV[R]_n) :
  (I == (0 : 'rV[R]_m))%IS = (I == 0).
Proof.
apply/andP/idP.
- by rewrite subid_eq0; case.
by move/eqP ->; split; apply/subidP; exists 0; rewrite mulmx0.
Qed.

Lemma subid1 m (I : 'rV[R]_m) : (I <= 1)%IS.
Proof. by apply/subidP; exists I; rewrite mul1mx. Qed.

Lemma subid_refl m (I : 'rV[R]_m) : (I <= I)%IS.
Proof. by apply/subidP; exists 1%:M; rewrite mulmx1. Qed.

Hint Resolve subid_refl.

Lemma eqid_refl m (I : 'rV[R]_m) : (I == I)%IS.
Proof. by rewrite !subid_refl. Qed.

Lemma eqid_sym m n (I: 'rV[R]_n) (J: 'rV[R]_m) :
  (I == J)%IS = (J == I)%IS.
Proof.
by apply/andP/andP => [[h1 h2] | [h1 h2]]; split.
Qed.

Lemma subid_trans m n k (J : 'rV_n) (I : 'rV[R]_m) (K : 'rV_k) :
  (I <= J -> J <= K -> I <= K)%IS.
Proof.
case/subidP=> X hX /subidP [Y hY].
apply/subidP.
exists (Y *m X).
by rewrite mulmxA -hY.
Qed.

Lemma eqid_trans m n k (J : 'rV_n) (I : 'rV[R]_m) (K : 'rV_k) :
  (I == J -> J == K -> I == K)%IS.
Proof.
case/andP=> h1 h2 /andP [h3 h4].
by rewrite (subid_trans h1 h3) (subid_trans h4 h2).
Qed.

Lemma subid_castmxl m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (h: m = p):
  ((castmx (erefl _,h) I) <= J)%IS = (I <= J)%IS.
Proof.
apply/subidP/subidP => [[D /rowP hD]|[D ->]].
- exists (castmx (erefl,esym h) D).
  apply/rowP => i.
  move: (hD (cast_ord h i)).
  rewrite !castmxE !mxE /= cast_ordK.
  have -> : cast_ord (erefl 1%nat) 0 = 0 by apply/ord_inj.
  move ->; apply/eq_big => // k _.
  by rewrite castmxE /= esymK cast_ord_id.
exists (castmx (erefl,h) D).
apply/rowP => i; rewrite !mxE !castmxE !mxE.
apply/eq_big => // k _ /=.
by rewrite castmxE /= !cast_ord_id.
Qed.

Lemma subid_castmxr m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (h: n = p):
  (I <= (castmx (erefl _,h) J))%IS = (I <= J)%IS.
Proof.
pose f := fun x => cast_ord (esym h) x.
pose f' := fun x => cast_ord h x.
apply/subidP/subidP => [[D /rowP hD]|[D ->]].
- exists (castmx (esym h,erefl _) D).
  apply/rowP => i.
  move: (hD i) => ->.
  rewrite !mxE (reindex_onto f f') /=; last first.
  + rewrite /f /f' => x _.
    by apply/ord_inj.
  apply/eq_big => // k.
  + rewrite /f' /f'; symmetry.
    by apply/eqP/ord_inj.
  by rewrite !castmxE /= !cast_ord_id cast_ordK => _.
exists (castmx (h, erefl _) D).
apply/rowP => i.
rewrite !mxE (reindex_onto f f'); last by rewrite /f /f' => x _; apply/ord_inj.
apply/eq_big => // k; first by rewrite /f' /f; apply/eqP/ord_inj.
by rewrite !castmxE /= !cast_ord_id.
Qed.


(** Ideal addition *)

Definition addid m n (I : 'rV[R]_m) (J : 'rV[R]_n) := row_mx I J.

Local Notation "I +i J" := (addid I J) (at level 30).

Lemma sub_add0rid m n (I : 'rV[R]_m) : (I +i (0 : 'rV[R]_n) <= I)%IS.
Proof.
apply/subidP.
exists (pid_mx m).
by rewrite pid_mx_row mul_mx_row mulmx1 mulmx0.
Qed.

Lemma sub_addid0r m n (I : 'rV[R]_m) : (I <= I +i (0 : 'rV[R]_n))%IS.
Proof.
apply/subidP.
exists (pid_mx m).
by rewrite pid_mx_col mul_row_col mulmx1 mulmx0 addr0.
Qed.

Lemma subid_addC m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  (I +i J <= J +i I)%IS.
Proof.
apply/subidP.
exists (block_mx 0 1%:M 1%:M 0).
by rewrite mul_row_col !mul_mx_row !mulmx0 !mulmx1 add_row_mx addr0 add0r.
Qed.

Lemma subid_addAl m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p) :
  (I +i (J +i K) <= (I +i J) +i K)%IS.
Proof.
apply/subidP.
exists (block_mx (col_mx 1%:M 0) (block_mx 0 0 1%:M 0) 0 (row_mx 0 1%:M)).
rewrite mul_row_col !mul_mx_row add_row_mx !mulmx0 mulmx1 addr0 !mul_row_col.
by rewrite !mul_mx_row !mulmx0 row_mx0 !mulmx1 addr0 add0r add_row_mx addr0 add0r.
Qed.

Lemma subid_addAr m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p) :
  ((I +i J) +i K <= I +i (J +i K))%IS.
Proof.
apply/subidP.
exists (block_mx (row_mx 1%:M 0) 0 (block_mx 0 1%:M 0 0) (col_mx 0 1%:M)).
rewrite mul_row_col !mul_mx_row add_row_mx !mulmx0 mulmx1 !mul_row_col.
by rewrite !mul_mx_row !mulmx0 row_mx0 !mulmx1 addr0 add0r add_row_mx addr0 !add0r.
Qed.

Lemma sub_add0lid m n (I : 'rV[R]_n) : ((0 : 'rV[R]_m) +i I <= I)%IS.
Proof. exact: (subid_trans (subid_addC 0 I) (sub_add0rid m I)). Qed.

Lemma sub_addid0l m n (I : 'rV[R]_n) : (I <= (0 : 'rV[R]_m) +i I)%IS.
Proof. exact: (subid_trans (sub_addid0r _ _) (subid_addC I 0)). Qed.

Lemma addid0 m n (I : 'rV[R]_m) : (I +i (0 : 'rV[R]_n) == I)%IS.
Proof. by rewrite sub_addid0r sub_add0rid. Qed.

Lemma add0id m n (I : 'rV[R]_m) : ((0 : 'rV[R]_n) +i I == I)%IS.
Proof. by rewrite sub_addid0l sub_add0lid. Qed.

Lemma addidC m n (I : 'rV[R]_m) (J : 'rV[R]_n) : (I +i J == J +i I)%IS.
Proof. by rewrite !subid_addC. Qed.

Lemma addid_addA m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p):
  (I +i (J +i K) == (I +i J) +i K)%IS.
Proof. by rewrite subid_addAl subid_addAr. Qed.

Lemma sub_addidl m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p):
  (J <= K)%IS -> (I +i J <= I +i K)%IS.
Proof.
case/subidP => D hD; apply/subidP.
exists (block_mx 1%:M 0 0 D).
by rewrite hD mul_row_col !mul_mx_row !mulmx0 add_row_mx addr0 add0r mulmx1.
Qed.

Lemma sub_addidr m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p):
  (J <= K)%IS -> (J +i I <= K +i I)%IS.
Proof.
case/subidP => D hD; apply/subidP.
exists (block_mx D 0 0 1%:M).
by rewrite hD mul_row_col !mul_mx_row !mulmx0 add_row_mx addr0 add0r mulmx1.
Qed.

Lemma add_addil m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p) :
  (J == K)%IS -> (I +i J == I +i K)%IS.
Proof. by case/andP => hJK hKJ; rewrite sub_addidl // sub_addidl. Qed.

Lemma add_addir m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p) :
  (J == K)%IS -> (J +i I == K +i I)%IS.
Proof. by case/andP => hJK hKJ; rewrite sub_addidr // sub_addidr. Qed.

Lemma subid_addid_congr m n p (I : 'rV[R]_n) (J : 'rV[R]_m) (K : 'rV[R]_p) :
  (I <= K)%IS -> (J <= K)%IS -> (I +i J <= K)%IS.
Proof.
case/subidP => C hC /subidP [D hD]; apply/subidP.
by exists (row_mx C D); rewrite /addid mul_mx_row -hC -hD.
Qed.

Lemma addid_congr m n p o (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p) (L : 'rV_o) :
  (I <= K -> J <= L -> I +i J <= K +i L)%IS.
Proof.
case/subidP => X hX.
case/subidP => Y hY.
apply/subidP.
exists (block_mx X 0 0 Y).
by rewrite mul_row_block !mulmx0 addr0 add0r hX hY.
Qed.

Lemma scale_addid (x: R) m n (I : 'rV[R]_m) (J: 'rV[R]_n):
  x *: (I +i J) = (x *: I) +i (x *: J).
Proof. by rewrite /addid -scale_row_mx. Qed.

Lemma subid_scaleid (x: R) m n (I: 'rV[R]_m) (J: 'rV[R]_n):
  x != 0 -> (I <= J)%IS = (x *: I <= x *: J)%IS.
Proof.
move=> x0.
apply/idP/idP; case/subidP => D hD; apply/subidP; exists D.
  by rewrite hD -scalemxAl.
apply/eqP.
by rewrite -(inj_eq (scalemx_inj x0)) hD -!mul_scalar_mx mulmxA.
Qed.

Lemma eqid_scaleid (x: R) m n (I: 'rV[R]_m) (J: 'rV[R]_n):
  x != 0 -> (I == J)%IS = (x *: I == x *: J)%IS.
Proof.
move=>x0; apply/idP/idP.
  by rewrite (@subid_scaleid x) //; case/andP=> ->; rewrite (@subid_scaleid x).
case/andP.
by rewrite -(@subid_scaleid x) // => ->; rewrite -(@subid_scaleid x) // => ->.
Qed.


(** Ideal multiplication *)

Definition mulid m n (I : 'rV[R]_m) (J : 'rV[R]_n) : 'rV[R]_(m * n) :=
  mxvec (I^T *m J).

Local Notation "I *i J" := (mulid I J) (at level 50).

Lemma tr_mxvec_subid m n (I : 'M[R]_(m,n)) : (mxvec I <= mxvec I^T)%IS.
Proof.
apply/subid_in => i.
case/mxvec_indexP: i => i j.
exists (mxvec_index j i).
by rewrite !mxvecE mxE.
Qed.

Lemma mxvec_r1l m (I: 'rV[R]_m) : (mxvec I <= I)%IS.
Proof.
apply/subid_in => i.
case/mxvec_indexP : i => i j; rewrite !ord1 {i}.
rewrite mxvecE.
by exists j.
Qed.

Lemma mxvec_r1r m (I: 'rV[R]_m) : (I <= mxvec I)%IS.
Proof.
apply/subid_in => i.
exists (mxvec_index 0 i).
by rewrite mxvecE.
Qed.

Lemma mulid0 m n p (I: 'rV[R]_m) : (I *i (0: 'rV[R]_n) == (0: 'rV[R]_p))%IS.
Proof.
apply/andP; split; last by apply/sub0id.
rewrite /mulid mulmx0 mxvec0.
apply/subidP; by exists 0; rewrite mul0mx.
Qed.

Lemma subid_mulC m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  (mulid I J <= mulid J I)%IS.
Proof. by rewrite (subid_trans (tr_mxvec_subid _)) // trmx_mul trmxK. Qed.

Lemma mulidC m n (I : 'rV[R]_m) (J : 'rV[R]_n) : (mulid I J == mulid J I)%IS.
Proof. by rewrite !subid_mulC. Qed.

Lemma sub_mulidl m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p):
  (J <= K -> I *i J <= I *i K)%IS.
Proof.
case/subidP => D hD; apply/subidP.
exists (lin_mulmxr D).
apply: (canLR vec_mxK).
by rewrite mx_vec_lin /= -mulmxA -hD.
Qed.

Lemma sub_mulidr m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p) :
  (J <= K -> J *i I <= K *i I)%IS.
Proof.
move=> h.
apply/(subid_trans (subid_mulC _ _))/(subid_trans _ (subid_mulC _ _)).
by apply/sub_mulidl.
Qed.

Lemma subid_mulidAl l m n (K : 'rV[R]_l) (I : 'rV[R]_m) (J : 'rV[R]_n) :
  (I *i (J *i K) <= (I *i J) *i K)%IS.
Proof.
rewrite /mulid; apply/subid_in => i.
case/mxvec_indexP : i => i x.
rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
case/mxvec_indexP : x => j k.
rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
exists (mxvec_index (mxvec_index i j) k).
rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
by rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE mulrA.
Qed.

Lemma subid_mulidAr l m n (K : 'rV[R]_l) (I : 'rV[R]_m) (J : 'rV[R]_n) :
  ((I *i J) *i K <= I *i (J *i K))%IS.
Proof.
rewrite /mulid; apply/subid_in => i.
case/mxvec_indexP : i => x k.
rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
case/mxvec_indexP : x => i j.
rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
exists (mxvec_index i (mxvec_index j k)).
rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
by rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE mulrA.
Qed.

Lemma mulidA l m n (K : 'rV[R]_l) (I : 'rV[R]_m) (J : 'rV[R]_n) :
  ((I *i J) *i K == I *i (J *i K))%IS.
Proof. by rewrite subid_mulidAl subid_mulidAr. Qed.

Lemma mulid_addidr m n k (I : 'rV[R]_m) (J : 'rV[R]_n) (K : 'rV[R]_k) :
  (I *i (J +i K) <= (I *i J) +i (I *i K))%IS.
Proof.
rewrite /mulid; apply/subid_in => i.
case/mxvec_indexP : i => i x.
rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
case: splitP => j hj.
  exists (lshift (m*k)%nat (mxvec_index i j)).
  rewrite !mxE.
  case: splitP => ij /= hij.
    case/mxvec_indexP : ij hij => a b /= hab.
    have : enum_rank (i,j) = enum_rank (a,b) by apply/ord_inj.
    case/enum_rank_inj => -> ->.
    by rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
  case/mxvec_indexP : ij hij => a b /= hab.
  have : ~ (enum_rank (i,j) < (m * n)%nat)
    by rewrite hab -{2}[(m * n)%nat]addn0 ltn_add2l ltn0.
  case.
  by apply (leq_trans (ltn_ord _)); rewrite /= eq_card_prod // !card_ord.
exists (rshift (m*n)%nat (mxvec_index i j)).
rewrite !mxE.
case: splitP => ij /= hij.
  case/mxvec_indexP : ij hij => a b /= hab.
  have : ~ (enum_rank (a,b) < (m * n)%nat)
    by rewrite -hab -{2}[(m * n)%nat]addn0 ltn_add2l ltn0.
  case.
  by apply (leq_trans (ltn_ord _)); rewrite /= eq_card_prod // !card_ord.
case/mxvec_indexP : ij hij => a b /= hab.
have : enum_rank (i,j) = enum_rank (a,b).
  apply/ord_inj/eqP.
  by rewrite -(eqn_add2l (m * n)%nat) hab.
case/enum_rank_inj => -> ->.
by rewrite mxvecE !mxE big_ord_recl big_ord0 addr0 !mxE.
Qed.

Lemma scale_mulidr a n m (I : 'rV[R]_n) (J : 'rV[R]_m) :
  (a *: (I *i J) == (a *: I) *i J)%IS.
Proof.
rewrite /mulid -!mul_scalar_mx trmx_mul tr_scalar_mx -mulmxA !mul_scalar_mx.
by rewrite -scalemxAr scale_mxvec eqid_refl.
Qed.

Lemma scale_mulidl a n m (I : 'rV[R]_n) (J : 'rV[R]_m) :
  ((a *: I) *i J <= a *: (I *i J))%IS.
Proof. by case/andP: (scale_mulidr a I J). Qed.

Lemma subid_mulid_congr m n p o
  (I : 'rV[R]_m) (J : 'rV[R]_n) (K : 'rV[R]_p) (L : 'rV_o) :
  (I <= K)%IS -> (J <= L)%IS -> (I *i J <= K *i L)%IS.
Proof.
move => h1 h2.
by apply/(subid_trans (sub_mulidl _ h2))/(sub_mulidr _ h1).
Qed.

Lemma mulid_congr m n p q (I: 'rV[R]_m) (J: 'rV[R]_n)
  (K: 'rV[R]_p) (L: 'rV[R]_q) :
  (I == K)%IS -> (J == L)%IS -> (I *i J == K *i L)%IS.
Proof.
case/andP => h1 h2 /andP [h3 h4]; apply/andP; split.
- by apply/(subid_trans (sub_mulidl _ h3))/(sub_mulidr _ h1).
by apply/(subid_trans (sub_mulidl _ h4))/(sub_mulidr _ h2).
Qed.

Lemma scaleidE m a (I: 'rV[R]_m) : (a *: I == (a%:M : 'M[R]_1) *i I)%IS.
Proof.
rewrite /mulid tr_scalar_mx mul_scalar_mx scale_mxvec.
case ha : (a == 0).
- rewrite (eqP ha) !scale0r.
  by apply/andP; split; apply/subidP; exists 0; rewrite mul0mx.
by rewrite -eqid_scaleid ?mxvec_r1l ?mxvec_r1r // ha.
Qed.


(** A version of mxvec and ideal multiplication that is more suitable for
   implementation as a computable version *)
Fixpoint flattenmx m n : 'M[R]_(m,n) -> 'rV[R]_(m * n) :=
  match m return 'M[R]_(m,n) -> 'rV[R]_(m * n) with
  | O => fun _ => 0
  | S p => fun (M : 'M[R]_(1 + p,n)) => row_mx (usubmx M) (flattenmx (dsubmx M))
  end.

(** Every element in flattenmx is in mxvec *)
Lemma flattenmx_in_mxvec : forall m n (M : 'M[R]_(m,n)) i,
  exists j, ((mxvec M) 0 j = (flattenmx M) 0 i).
Proof.
elim => [n M []|m ih n] //.
rewrite [m.+1]/(1 + m)%N => M i /=.
rewrite !mxE.
case: splitP => j hj.
  exists (mxvec_index 0 j).
  by rewrite mxvecE !mxE lshift0.
case: (ih _ (dsubmx M) j) => k hk.
case/mxvec_indexP: k hk => a b.
rewrite mxvecE !mxE rshift1 => hh.
exists (mxvec_index (lift 0 a) b).
by rewrite mxvecE.
Qed.

Lemma flattenmx_mxvec m n (M : 'M[R]_(m,n)) : (flattenmx M <= mxvec M)%IS.
Proof. by apply/subid_in/flattenmx_in_mxvec. Qed.

(** Build the correct index in flattenmx *)
Lemma flattenmx_index_proof (m n : nat) : forall (i : 'I_m) (j : 'I_n),
  (i * n + j < m * n)%N.
Proof.
move=> [i hi] [j hj] /=.
case: m hi => //= m; rewrite ltnS => hi.
case: n hj => //= n; rewrite ltnS => hj.
rewrite !mulSn !mulnS addSn ltnS -addnA [(n + _)%N]addnCA.
apply: leq_add => //; rewrite addnC.
by apply: leq_add => //; rewrite leq_mul2r hi orbT.
Qed.

Definition flattenmx_index (m n : nat) (i : 'I_m) (j : 'I_n) :=
  Ordinal (flattenmx_index_proof i j).

Lemma flattenmx_indexE : forall m n (M : 'M[R]_(m,n)) (i : 'I_m) (j : 'I_n),
  (flattenmx M) 0 (flattenmx_index i j) = M i j.
Proof.
elim => [m M []|] //.
rewrite /flattenmx_index /= => m ih n.
rewrite [m.+1]/(1 + m)%N => M i j.
rewrite -{3}[M]vsubmxK !mxE.
case: splitP => /= k hk.
  case: splitP => /= l hl.
    rewrite ord1 !mxE lshift0.
    move: hk.
    by rewrite hl ord1 mul0n add0n => /ord_inj ->.
  case: k hk => /= k hk h.
  suff hnk : n <= k by move: (leq_ltn_trans hnk hk); rewrite ltnn.
  move: h.
  by rewrite hl mulnDl mul1n => <-; rewrite -{1}[n]addn0 -addnA leq_add2l.
case: splitP => l hl.
  rewrite hl !ord1 mul0n add0n in hk.
  case: j hk => /= j hj hk.
  move: hj; rewrite hk => hj.
  suff : (n + k < n) -> false by move => /(_ hj).
  by rewrite -ltn_subRL subnn.
move: (ih _ (dsubmx M) l j); rewrite !mxE => <-.
f_equal; apply/ord_inj => /=.
move: hk; rewrite hl mulnDl mul1n -addnA => /eqP.
by rewrite eqn_add2l => /eqP ->.
Qed.

(** Every element in mxvec is in flattenmx *)
Lemma mxvec_in_flattenmx m n (M : 'M[R]_(m,n)) i :
  exists j, ((flattenmx M) 0 j = (mxvec M) 0 i).
Proof.
case/mxvec_indexP: i => i j; rewrite mxvecE.
exists (flattenmx_index i j).
by rewrite flattenmx_indexE.
Qed.

Lemma mxvec_flattenmx m n (M : 'M[R]_(m,n)) : (mxvec M <= flattenmx M)%IS.
Proof. by apply/subid_in/mxvec_in_flattenmx. Qed.

(** The inverse of flattenmx_index *)
Lemma flattenmx_indexP m n (k : 'I_(m * n)) : exists i j,
  k = flattenmx_index i j.
Proof.
have n0 : 0 < n by case: n k => // [[l]]; rewrite muln0.
have h1 : (k %/ n < m) by rewrite ltn_divLR.
have h2 : (k %% n < n) by rewrite ltn_mod.
exists (Ordinal h1); exists (Ordinal h2).
apply/ord_inj => /=.
exact: (divn_eq k n).
Qed.

(** Alternative version of ideal multiplication that is more suitable
   for computation as the behavior is more predictable than the one
   based on mxvec *)
Definition mulidc m n (I : 'rV[R]_m) (J : 'rV[R]_n) := flattenmx (I^T *m J).

Lemma mulidcP m n (I : 'rV[R]_m) (J : 'rV[R]_n) : (I *i J == mulidc I J)%IS.
Proof.
by apply/andP; split; rewrite /mulid /mulidc ?mxvec_flattenmx ?flattenmx_mxvec.
Qed.

(** Every element in mulidc is in mulid *)
Lemma mulidc_in_mulid m n (I : 'rV[R]_m) (J : 'rV[R]_n) i :
  exists j, ((I *i J) 0 j = (mulidc I J) 0 i).
Proof. by rewrite /mulid /mulidc; apply/flattenmx_in_mxvec. Qed.

(* Special lemma that is just here for the computable version of ideal
   intersection in prufer domains... *)

Lemma mulidc_in_mulid2 : forall m n l (I : 'rV[R]_m) (J : 'rV[R]_n) (K : 'rV[R]_l) i,
  exists j, (((I *i J) *i K) 0 j = (mulidc (mulidc I J) K) 0 i).
Proof.
have temp : forall m n l (I : 'rV[R]_m) (J : 'rV[R]_n) (K : 'rV[R]_l) i,
           (forall i, exists j, I 0 j = K 0 i) ->
            exists j, ((I *i J) 0 j = (mulidc K J) 0 i).
  move=> m n l I J K i.
  case: (flattenmx_indexP i) => a [b ->] /(_ a) [x hx].
  exists (mxvec_index x b).
  rewrite /mulidc flattenmx_indexE mxvecE !mxE.
  apply: eq_big => // c _.
  by rewrite !mxE ord1 hx.
move=> m n l I J K i.
apply: temp => j.
case: (mulidc_in_mulid I J j) => k hk.
by exists k; rewrite hk.
Qed.


(** Ideal intersection *)

Section IdealIntersection.

Variable cap_size : forall n m, 'rV[R]_n -> 'rV[R]_m -> nat.

CoInductive int_spec m n (I : 'rV[R]_m) (J : 'rV[R]_n) : 'rV[R]_(cap_size I J).+1 -> Type :=
  IntSpec cap of (cap <= I)%IS
  & (cap <= J)%IS
  & (forall x, member x I -> member x J -> member x cap) : int_spec cap.

End IdealIntersection.

End IdealTheory.

End StronglyDiscreteTheory.

Notation "A <= B" := (subid A B) : ideal_scope.
Notation "A <= B <= C" := ((subid A B) && (subid B C)) : ideal_scope.
Notation "A == B" := ((subid A B) && (subid B A)) : ideal_scope.
Notation "I +i J" := (addid I J) (at level 30).
Notation "I *i J" := (mulid I J) (at level 50).

Section BezoutStronglyDiscrete.

Variable R : bezoutRingType.

Definition bmember n (x : R) (I : 'rV[R]_n) := match x %/? principal_gen I with
  | Some a => Some (principal_w1 I *m a%:M)
  | None   => None
end.

Lemma bmember_correct : forall n (x : R) (I : 'rV[R]_n),
  member_spec x I (bmember x I).
Proof.
rewrite /bmember => n x I.
case: odivrP => [a | ] Ha /=; constructor.
  by rewrite mulmxA principal_w1_correct Ha mulrC /principal scalar_mxM.
move => J.
rewrite -(principal_w2_correct I) /principal -mulmxA -scalar_mxC.
move: (Ha ((principal_w2 I *m J) 0 0)).
apply/contra.
rewrite {1}[principal_w2 I *m J]mx11_scalar -scalar_mxM.
move/eqP/matrixP => /(_ 0 0).
by rewrite !mxE /= !mulr1n => ->.
Qed.

Definition bezout_stronglyDiscreteMixin := StronglyDiscrete.Mixin bmember_correct.
Canonical Structure bezout_stronglyDiscreteType :=
  Eval hnf in StronglyDiscreteType R bezout_stronglyDiscreteMixin.

End BezoutStronglyDiscrete.