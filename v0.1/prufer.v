Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice.
Require Import matrix bigop zmodp mxalgebra poly.

Require Import dvdring stronglydiscrete coherent ssrcomplements.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** Prufer domains *)
Module PruferDomain.

Record mixin_of (R : ringType) : Type := Mixin {
  prufer: R -> R -> (R * R * R);
  _ : forall x y, let: (u,v,w) := prufer x y in
      u * x = v * y /\ (1 - u) * y = w * x
}.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base  : DvdRing.class_of R;
  mixin : mixin_of (DvdRing.Pack base R)
}.
Local Coercion base : class_of >-> DvdRing.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c T.

Definition pack b0 (m0 : mixin_of (@DvdRing.Pack T b0 T)) :=
  fun bT b & phant_id (DvdRing.class bT) b =>
  fun    m & phant_id m m0 => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition ringType := GRing.Ring.Pack class cT.
Definition comRingType := GRing.ComRing.Pack class cT.
Definition idomainType := GRing.IntegralDomain.Pack class cT.
Definition dvdRingType := DvdRing.Pack class cT.
End ClassDef.

Module Exports.
Coercion base : class_of >-> DvdRing.class_of.
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
Coercion dvdRingType : type >-> DvdRing.type.
Canonical Structure dvdRingType.

Notation pruferDomainType := type.
Notation PruferDomainType T m := (@pack T _ m _ _ id _ id).
Notation PruferDomainMixin := Mixin.
Notation "[ 'pruferDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'pruferDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pruferDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'pruferDomainType'  'of'  T ]") : form_scope.
End Exports.

End PruferDomain.
Export PruferDomain.Exports.

Definition prufer R := PruferDomain.prufer (PruferDomain.class R).

Section PrincipalLocMat.

(** Definition of what principal localization matrices are *)
Variable R: ringType.

Definition P1 m (M: 'M[R]_m) :=
   \big[+%R/0]_(i: 'I_m) (M i i) = (0 < m)%:R.

Definition P2 m (X: 'rV[R]_m) (M: 'M[R]_m) :=
  forall (i j l: 'I_m), (M l j) * (X 0 i) = (M l i) * (X 0 j).

Definition isPLM m (L: 'rV[R]_m) (M: 'M[R]_m) :=
  P1 M /\ P2 L M.

End PrincipalLocMat.

Section PruferDomainTheory.

Variable R : pruferDomainType.

Lemma pruferP : forall (x y: R) ,
  let: (u,v,w) := prufer x y in u * x = v * y /\ (1 - u) * y = w * x.
Proof. by case: R => [? [? []]]. Qed.

Definition pruferAlt (x y : R) := let: (u,v,w) := prufer x y in
  (u,v,w,1 - u).

Lemma pruferAltP (x y : R) :
  let: (u,v,w,t) := pruferAlt x y in
     u + t = 1 /\ u * x = v * y /\ w * x = t * y.
Proof.
rewrite /pruferAlt.
case: prufer (pruferP x y) => [[u v] w] [h1 h2]; split => //.
by rewrite addrCA subrr addr0.
Qed.

(** Compute a principal localization matrix from an ideal *)
Fixpoint plm m {struct m} : 'rV[R]_m -> 'M[R]_m :=
  if m == 1%N then (fun _ => 1%:M) else
  match m return 'rV[R]_m -> 'M[R]_m with
    | S p => fun (L: 'rV[R]_(1 + p)) =>
      let: u := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).1.1.1 in
      let: v := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).1.1.2 in
      let: w := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).1.2 in
      let: t := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).2 in
      let B : 'M[R]_p := plm (rsubmx L) in
        \matrix_(i < 1 + p, j < 1 + p)(
          match (split i),(split j) with
            | inl _, inl _ => \big[+%R/0]_k (B k k * t k)
            | inl _, inr y => \big[+%R/0]_k (B k y * w k)
            | inr x, inl _ => B x x * v x
            | inr x, inr y => B x y * u x
          end)
    | O => fun _ => 1%:M
  end.

Lemma plmP : forall m (L: 'rV[R]_m), isPLM L (plm L).
Proof.
rewrite /isPLM /P1 /P2; elim => [ L | m hi] /=.
  by rewrite big_ord0; split=> // [[]].
case: m hi=> [_ L|m hi].
  by rewrite eqxx big_ord1 !mxE eqxx; split=> // i j l; rewrite !ord1 !mxE.
rewrite [m.+2]/(1 + (1 + m))%nat => L.
case: (hi (rsubmx L))=> {hi}.
have -> : (m.+2 == 1%N) = false by [].
have -> : (0 < m.+1)%:R = 1 by [].
set B : 'M[R]_(1 + m) := plm (rsubmx L) => h1 h2.
set u := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).1.1.1.
set v := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).1.1.2.
set w := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).1.2.
set t := fun i => (pruferAlt (L 0 0) (L 0 (lift 0 i))).2.
have huti : forall i, u i + t i = 1.
  rewrite /u /t => i; move: (pruferAltP (L 0 0) (L 0 (lift 0 i))).
  by case: pruferAlt => [[[U V] W ] T []].
have huvi : forall i, u i * (L 0 0) = v i * (L 0 (lift 0 i)).
  rewrite /u /v => i; move: (pruferAltP (L 0 0) (L 0 (lift 0 i))).
  by case: pruferAlt => [[[U V] W] T] [_ []].
have hwti : forall i, w i * (L 0 0) = t i * (L 0 (lift 0 i)).
  rewrite /w /t => i; move: (pruferAltP (L 0 0) (L 0 (lift 0 i))).
  by case: pruferAlt => [[[U V] W] T] [_ []].
split.
  rewrite big_ord_recl.
  have : \big[+%R/0]_(i < m.+1) (B i i * t i + B i i * u i) = 1.
    have <- : \big[+%R/0]_(i < m.+1) (B i i * (t i + u i)) = 1.
      by rewrite -h1; apply/eq_big => // i _; rewrite addrC huti mulr1.
    by apply/eq_big => // i _; rewrite mulrDr.
  rewrite big_split [X in X -> _]/= => <-; congr (_ + _).
    by rewrite !mxE; case: splitP.
  apply/eq_big => // i _; rewrite !mxE.
  case: splitP => x; first by rewrite ord1.
  move/eqP; rewrite eqSS => /eqP hx.
  by have -> : i = x by apply/ord_inj.
move => i j l; rewrite !mxE -/plm.
case: splitP => xl; rewrite ?ord1 => hl.
  case: splitP => xj; rewrite ?ord1 => hj.
    have -> : j = 0 by apply/ord_inj.
    case: splitP => xi {hj j}; rewrite ?ord1 => hi.
      by have -> : i = 0 by apply/ord_inj.
    have -> : i = lift 0 xi by apply/ord_inj.
    rewrite !big_distrl /=; apply/eq_big => // k _ {i hi}.
    move: (h2 xi k k); rewrite mulrAC !mxE !rshift1 => ->.
    by rewrite -!mulrA; congr (_ * _); rewrite mulrC hwti.
  have -> : j = lift 0 xj by apply/ord_inj.
  case: splitP => xi {j hj}; rewrite ?ord1 => hi.
    have -> : i = 0 by apply/ord_inj.
    rewrite !big_distrl /=; apply/eq_big => // k _ {i hi}.
    symmetry.
    move: (h2 xj k k); rewrite mulrAC !mxE !rshift1 => ->.
    by rewrite -!mulrA; congr (_ * _); rewrite mulrC hwti.
  have -> : i = lift 0 xi by apply/ord_inj.
  rewrite !big_distrl /=; apply/eq_big => // k _ {i hi}.
  rewrite mulrAC [X in _ = X]mulrAC; congr (_ * _).
  by move: (h2 xi xj k); rewrite !mxE !rshift1.
case: splitP => xj; rewrite ?ord1 => hj.
  have -> : j = 0 by apply/ord_inj.
  case: splitP => xi; rewrite ?ord1 => hi.
    by have -> : i = 0 by apply/ord_inj.
  have -> : i = lift 0 xi by apply/ord_inj.
  rewrite {j i hj hi} mulrAC [X in _ = X]mulrAC [X in _ = X]mulrC.
  move: (h2 xi xl xl); rewrite !mxE !rshift1 => ->.
  by rewrite mulrCA huvi -mulrA; congr (_ * _); rewrite mulrC.
have -> : j = lift 0 xj by apply/ord_inj.
case: splitP => xi {j hj}; rewrite ?ord1 => hi.
  have -> : i = 0 by apply/ord_inj.
  rewrite mulrAC mulrC; symmetry; rewrite mulrAC.
  move: (h2 xj xl xl); rewrite !mxE !rshift1 => ->.
  by rewrite mulrAC -mulrA -huvi mulrCA.
have -> : i = lift 0 xi by apply/ord_inj.
move: (h2 xi xj xl); rewrite !mxE !rshift1 mulrAC => ->.
by rewrite mulrAC.
Qed.

Lemma col_plm_mull n (I : 'rV[R]_n.+1) i :
  (col i (plm I)) *m I = (I 0 i) *: (plm I).
Proof.
apply/matrixP => j l; rewrite !mxE.
case: (plmP I); rewrite /P1 /P2 => h1 h2.
by rewrite big_ord_recl big_ord0 addr0 !mxE h2 mulrC.
Qed.

(** The columns of the PLM give the inverse of the ideal *)
Lemma col_plm_mulr n (I : 'rV[R]_n.+1) i : I *m col i (plm I) = (I 0 i)%:M.
Proof.
case: (plmP I); set M := plm _; rewrite /P1 /P2 => h1 h2.
apply/matrixP=> j l; rewrite !ord1 !mxE eqxx mulr1n {j l}.
have -> : \sum_j0 (I 0 j0 * (col i M) j0 0) = \sum_j0 (I 0 i * M j0 j0).
  apply: eq_bigr=> j0 _.
  by rewrite !mxE mulrC -h2 mulrC.
by rewrite -big_distrr /= h1 mulr1.
Qed.

End PruferDomainTheory.

(** Bezout rings are Prufer domains *)
Section BezoutRing_is_Prufer.

Variable R : bezoutRingType.

Definition bezout_calc (x y: R) : (R * R * R)%type :=
  let: (g,c,d,a,b) := egcdr x y in (d * b, a * d, b * c).

Lemma bezout_calcP (x y : R) :
  let: (u,v,w) := bezout_calc x y in u * x = v * y /\ (1 - u) * y = w * x.
Proof.
rewrite /bezout_calc.
case: egcdrP => g c d a b h1 hg hx hy; split.
- by rewrite hx hy mulrCA !mulrA.
by rewrite hx hy -h1 -addrA subrr addr0 mulrCA !mulrA.
Qed.

Definition bezout_pruferMixin :=
  PruferDomainMixin bezout_calcP.
Canonical Structure bezout_pruferType :=
  Eval hnf in PruferDomainType R bezout_pruferMixin.

End BezoutRing_is_Prufer.


(** Proof that Prufer domains are strongly discrete (this is only true
   as divisibility is explicit) *)
Section StronglyDiscrete.

Variable R : pruferDomainType.

Definition pmember n (x : R) : 'rV[R]_n -> option 'cV[R]_n := match n with
  | S p => fun (I : 'rV[R]_p.+1) =>
      let a := plm I in
      if [forall i, I 0 i %| a i i * x]
         then Some (\col_i odflt 0 (a i i * x %/? I 0 i))
         else None
  | _ => fun _ => if x == 0 then Some 0 else None
end.

Lemma pmember_correct : forall n (x : R) (I : 'rV[R]_n),
  member_spec x I (pmember x I).
Proof.
case=> [|n] x I; rewrite /pmember.
  rewrite thinmx0.
  case: ifP => [/eqP ->|h]; constructor. 
    rewrite mulmx0.
    by have -> : 0%:M = 0 by move=> *; apply/matrixP => i j; rewrite !mxE mul0rn.
  by move => J; rewrite mul0mx -scalemx1 scalemx_eq0 h oner_neq0.
set M := plm _.
case: ifP => /forallP hdvd; constructor.
  apply/rowP => i; rewrite !ord1 !mxE mulr1n  {i}.
  case: (plmP I); rewrite /isPLM /P1.
  have -> : (0 < n.+1)%:R = 1 by [] => h1 _.
  rewrite -[x]mul1r -h1 big_distrl.
  set N := plm _ => /=.
  apply/eq_big => // i _; rewrite !mxE.
  case: odivrP => [a | ] /=.
  + rewrite [X in _ = X]mulrC/= => <-.
    by rewrite -big_distrl /= h1 mul1r.
  case/dvdrP: (hdvd i) => b hb /(_ b).
  by rewrite -big_distrl /= h1 mul1r hb eqxx.
move => J; apply/eqP => /rowP  /(_ 0).
rewrite !mxE mulr1n => heq.
apply: hdvd => i; rewrite heq.
rewrite big_distrr /=.
suff -> : \sum_j (M i i * (I 0 j * J j 0)) = \sum_j (I 0 i * (M i j * J j 0))
  by rewrite -big_distrr dvdr_mulr.
apply/eq_big => // j _.
case: (plmP I); rewrite mulrA /isPLM /P2 => _ ->.
by rewrite mulrCA mulrA.
Qed.

Definition prufer_stronglyDiscreteMixin :=
  StronglyDiscrete.Mixin pmember_correct.
Canonical Structure prufer_stronglyDiscreteType :=
  Eval hnf in StronglyDiscreteType R prufer_stronglyDiscreteMixin.

End StronglyDiscrete.

(** Some ideal theory of prufer domains *)
Section PruferIdeals.

Variable R : pruferDomainType.

(** Compute the i:th inverse of an ideal *)
Definition inv_id n (i : 'I_n) (I : 'rV[R]_n) : 'rV[R]_n := (col i (plm I))^T.

Lemma inv_idP1 : forall n (I: 'rV[R]_n) j, (inv_id j I *i I <= (I 0 j)%:M)%IS.
Proof.
case=> // n I j.
rewrite /inv_id /mulid trmxK col_plm_mull scale_mxvec -scalemx1.
case i0: (I 0 j == 0).
  by rewrite (eqP i0) !scale0r; apply/subidP; exists 0; rewrite mulmx0.
by rewrite -subid_scaleid ?subid1 // i0.
Qed.

Lemma inv_idP2 : forall n (I: 'rV[R]_n) j, ((I 0 j)%:M <= inv_id j I *i I)%IS.
Proof.
case=> [|n] I j; first by rewrite thinmx0 /= !mxE eqxx mulr1n member0.
rewrite /inv_id /mulid trmxK col_plm_mull scale_mxvec -scalemx1.
case i0: (I 0 j == 0).
  by rewrite (eqP i0) !scale0r; apply/subidP; exists 0; rewrite mulmx0.
rewrite -subid_scaleid ?i0 //.
case: (plmP I); rewrite /P1 => h1 _.
set m := (n.+1 * n.+1)%N.
pose p (i : 'I_m) := [exists j, i == mxvec_index j j].
apply/subidP.
exists (\col_(i < m) (p i)%:R).
apply/rowP => i.
rewrite !mxE ord1 eqxx (bigID p) /= addrC big1; last first.
  by move=> k; rewrite mxE => /negbTE ->; rewrite mulr0.
rewrite add0r (reindex (fun i => mxvec_index i i)) /=; last first.
  exists (fun (i : 'I_m) =>
              (enum_val (cast_ord (esym (mxvec_cast n.+1 n.+1)) i)).1) => x.
    by rewrite cast_ordK enum_rankK.
  rewrite inE; case/existsP => y /eqP ->.
  by rewrite cast_ordK enum_rankK.
rewrite -{1}h1.
have hp : forall k, p (mxvec_index k k) by move=> k; apply/existsP; exists k.
apply/eq_big=> k; first by symmetry; rewrite hp.
by rewrite mxvecE mxE hp mulr1.
Qed.

Lemma inv_idP n (I: 'rV[R]_n) j : (inv_id j I *i I == (I 0 j)%:M)%IS.
Proof. by rewrite inv_idP1 inv_idP2. Qed.

(** Ideals in Prufer domains have the cancellation property *)
Lemma subid_mulidKl m n p (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p):
  I != 0 -> (I *i J <= I *i K -> J <= K)%IS.
Proof.
move=> h0.
have h : exists j, (I 0 j != 0).
  have : ~ (forall j, I 0 j == 0).
    move => h; apply/eqP: h0.
    apply/eqP => /eqP; apply.
    by apply/rowP => i; rewrite (eqP (h i)) !mxE.
  move/forallP => h.
  by apply/existsP.
case: h => j hj /(sub_mulidl (inv_id j I)) hsub.
have h2 : ((inv_id j I *i I) *i J <= (inv_id j I *i I) *i K)%IS
  by rewrite (subid_trans (subid_mulidAr _ _ _)) ?(subid_trans hsub) //
             subid_mulidAl.
have : ((I 0 j)%:M *i J <= (I 0 j)%:M *i K)%IS.
  case/andP: (inv_idP I j) => hl hr.
  by rewrite (subid_trans (sub_mulidr _ hr)) ?(subid_trans h2) ?sub_mulidr.
rewrite /mulid tr_scalar_mx !mul_scalar_mx !scale_mxvec
  -subid_scaleid // => hleq.
by rewrite (subid_trans (mxvec_r1r J)) ?(subid_trans hleq) ?mxvec_r1l.
Qed.

End PruferIdeals.

(** Prufer domains are coherent *)
Section Coherent.

Variable R : pruferDomainType.

Definition pcap_size (n m : nat) (I : 'rV[R]_n) (J : 'rV[R]_m) :=
  (((n + m) * n) * m)%N.

Lemma pcap_size0 m (I: 'rV[R]_0) (J: 'rV[R]_m) : O = pcap_size I J.
Proof. by rewrite /pcap_size muln0 mul0n. Qed.

(* Find a nonzero element in a row vector - this is better to use than
   pick for computation *)
Fixpoint find_nonzero n : 'rV[R]_n -> option 'I_n := match n with
  | O => fun _ => None
  | S p => fun (I : 'rV[R]_(1 + _)%N) =>
    if I 0 0 != 0 then Some 0
                  else omap (fun i => lift 0 i) (find_nonzero (rsubmx I))
  end.

CoInductive find_nonzero_spec n (I : 'rV[R]_n) : option 'I_n -> Type :=
  | NonZero (x : 'I_n) of I 0 x != 0  : find_nonzero_spec I (Some x)
  | AllZero of (forall x, I 0 x == 0) : find_nonzero_spec I None.

Lemma find_nonzeroP : forall n (I : 'rV[R]_n),
  find_nonzero_spec I (find_nonzero I).
Proof.
elim => [I|n ih] /=; first by constructor; case.
rewrite [n.+1]/(1 + n)%N => I.
case: ifP => [h0|h1]; first by constructor.
case: (ih (rsubmx I)) => [i hi|h]; constructor.
  apply/contra: hi.
  by rewrite !mxE rshift1.
move=> i.
rewrite -[I]hsubmxK !mxE.
case: splitP => j hj; last by apply/h.
by rewrite ord1 !mxE lshift0; move/eqP: h1 => ->.
Qed.

(** Intersection of ideals in prufer domains *)
Definition pcap (n m : nat) (I : 'rV[R]_n) (J : 'rV[R]_m) :
  'rV[R]_(pcap_size I J).+1 := match find_nonzero (I +i J) with
  | Some i =>  let sIJ  := I +i J in
               let a    := sIJ 0 i in
               let acap := inv_id i sIJ *i I *i J in
               (0 : 'M_1) +i (\row_i (odflt 0 (acap 0 i %/? a)))
  | None => 0
  end.

Lemma destr : forall l n, n + l < n -> False.
Proof.
elim => [ nn | ll hi nn h]; first by rewrite addn0 ltnn.
by apply: (hi (nn.+1)); rewrite addSnnS (ltn_trans h).
Qed.

Lemma pcap_dvd : forall n m (I: 'rV[R]_n) (J: 'rV[R]_m) i j,
  (I +i J) 0 i %| (inv_id i (I +i J) *i I *i J) 0 j.
Proof.
rewrite /mulid => [[|n] m I J /= i j].
- rewrite thinmx0 !mxE.
  case: splitP => [[]|] // k /ord_inj ->.
  case/mxvec_indexP: j => a b.
  by rewrite mxvecE !mxE big_ord1 mulmx0 mxvec0 trmx0 !mxE mul0r dvdr0.
case: (plmP (I +i J)); rewrite /P1 /P2 -/plus => h1 h2.
case/mxvec_indexP: j; case/mxvec_indexP=> j o l.
rewrite mxvecE !mxE big_ord1 !mxE tr_mxvec mxvecE !mxE big_ord1 !mxE.
move: (h2 (rshift n.+1 l) i j).
case: splitP => k /= hk.
- move=> _.
  have hleq : (1 + n <= (n + m).+1)%nat
    by rewrite -[X in _ <= X]add1n leq_add2l -{1}[n]addn0 leq_add2l leq0n.
  have -> : i = widen_ord hleq k by apply/ord_inj.
  have := (h2 (widen_ord hleq k) (widen_ord hleq o) j).
  rewrite {hk i} !mxE.
  case: splitP => x hx.
  + case:splitP => y hy.
    * have <- : o = y by apply/ord_inj.
      have <- : x = k by apply/ord_inj.
      by move<-; rewrite -mulrA mulrCA dvdr_mulr.
    suff : ~ (o < (1 + n)%nat) by case.
    have -> : nat_of_ord o  = (n.+1 + y)%N by [].
    by rewrite add1n -{2}[n.+1]addn0 ltn_add2l ltn0.
  suff : ~ (k < (1 + n)%nat) by case.
  have -> : nat_of_ord k  = (n.+1 + x)%N by [].
  by rewrite add1n -{2}[n.+1]addn0 ltn_add2l ltn0.
rewrite !mxE.
case: splitP => l' /= hl; first by case: (@destr l n.+1); rewrite hl.
move/eqP: hl; rewrite eqn_add2l => /eqP hll.
have -> : l' = l by apply/ord_inj.
case: splitP => ii hi; first by case: (@destr k n.+1); rewrite -hk hi.
have -> : ii = k by move/eqP: hi; rewrite hk eqn_add2l => /eqP h; apply/ord_inj.
rewrite mulrAC => ->.
apply/dvdrP; exists ((plm (I +i J)) j (rshift n.+1 l) * I 0 o).
by rewrite mulrAC.
Qed.

(** Key property of ideals for coherence proof *)
Lemma pcap_id (n m : nat) (I : 'rV[R]_n) (J : 'rV[R]_m) :
  ((I +i J) *i pcap I J == I *i J)%IS.
Proof.
rewrite /pcap.
case: find_nonzeroP => [i|] hi; last first.
  apply: (eqid_trans (mulid0 _ (m*n) _)).
  rewrite eqid_sym eqid_eq0; apply/eqP.
  have h : I = 0.
  + suff : forall p, (I == (0 :'rV[R]_p))%IS
      by move => h; apply/eqP; rewrite -(eqid_eq0 n) h.
    move => p; rewrite eqid_eq0; apply/eqP/rowP => i; rewrite !mxE.
    move: (hi (lshift m i)); rewrite !mxE.
    case: splitP => ii /= hii /eqP.
    - by have -> : i = ii by apply/ord_inj.
    by case: (@destr ii n); rewrite -hii.
  by rewrite h /mulid trmx0 mul0mx mxvec0.
set sIJ  := I +i J.
set a    := sIJ 0 i.
set acap := inv_id i sIJ *i I *i J.
apply/(eqid_trans (mulid_congr (eqid_refl sIJ) (add0id 1 _))).
apply/(eqid_trans (mulidC _ _)); rewrite (@eqid_scaleid _ a) //.
apply/(eqid_trans (scale_mulidr a _ _)); rewrite -!mul_scalar_mx.
have -> : (a%:M *m \row_i odflt 0 (acap 0 i %/? a)) = acap.
  apply/rowP=>j.
  rewrite !mxE big_ord1 !mxE eqxx mulr1n.
  case: odivrP => /= [x|]; first by rewrite mulrC => <-.
  case/dvdrP: (pcap_dvd I J i j)=> x hx /(_ x).
  by rewrite hx eqxx.
rewrite /acap; move: (inv_idP sIJ i); rewrite -/a => h.
apply/(eqid_trans (mulidC _ _)).
apply/(eqid_trans (mulid_congr (eqid_refl _) (mulidA _ _ _))).
apply/(@eqid_trans _ _ _ _ ((sIJ *i (inv_id i sIJ)) *i (I *i J)));
  first by rewrite eqid_sym; apply/mulidA.
apply/(eqid_trans (mulid_congr (mulidC _ _) (eqid_refl _))).
apply/(@eqid_trans _ _ _ _ ((a%:M :'M[R]_1) *i (I *i J)));
  first by apply/mulid_congr => //; apply/eqid_refl.
by rewrite mul_scalar_mx eqid_sym scaleidE.
Qed.

Lemma subid_member_cancel m n p x (I: 'rV[R]_m) (J: 'rV[R]_n) (K: 'rV[R]_p) :
  I != 0 -> (I *i J <= I *i K)%IS -> member x J -> member x K.
Proof. by move => h0 h hJ; apply/(member_subid hJ)/(subid_mulidKl h0 h). Qed.

Lemma testF m n p (I : 'rV[R]_n) (J : 'rV[R]_m) (F : 'rV[R]_p):
  (F <= I)%IS -> (F <= J)%IS -> (F <= pcap I J)%IS.
Proof.
move => hF1 hF2.
case h0 : ((I +i J)%IS != 0); last first.
- move/negbT : h0; rewrite negbK => /eqP /rowP h0.
  have hI : I = 0.
  + apply/rowP => i.
    move: (h0 (lshift m i)); rewrite !mxE.
    case: splitP => ii /= hii; first by have -> : i = ii by apply/ord_inj.
    by case: (@destr ii n); rewrite -hii.
  have -> : F = 0
    by case/subidP : hF1; rewrite hI => D; rewrite mul0mx => ->.
  by apply/subidP; exists 0; rewrite mulmx0.
have h1 : ((I +i J) *i F <= I *i J)%IS.
- apply/(subid_trans (subid_mulC _ _))/(subid_trans (mulid_addidr _ _ _)).
  apply/subid_addid_congr; last by apply/subid_mulid_congr => //; apply/subid_refl.
  by apply/(subid_trans (subid_mulC _ _))/subid_mulid_congr; rewrite ?subid_refl.
have h2 : ((I +i J) *i F <= (I +i J) *i (pcap I J))%IS.
- case/andP: (pcap_id I J) => hl hr.
  by apply/(subid_trans _ hr).
by apply/(subid_mulidKl h0 h2).
Qed.

Lemma pcap0r m n (J: 'rV[R]_n) : pcap (0: 'rV[R]_m) J = 0.
Proof.
rewrite /pcap.
case: find_nonzeroP => //= i hJ.
set I := \row_j _.
suff : I = 0 by move => ->; rewrite /addid row_mx0.
apply/rowP => j; rewrite !mxE.
case: odivrP => //= a; rewrite /mulid.
case/mxvec_indexP : j => c r; rewrite mxvecE !mxE.
case/mxvec_indexP : c => l c.
rewrite big_ord_recl big_ord0 addr0 !mxE mxvecE !mxE.
rewrite big_ord_recl big_ord0 addr0 !mxE mulr0 mul0r.
move: hJ; rewrite !mxE.
case: splitP => li hli; first by rewrite !mxE eqxx.
move => hJ.
by rewrite -{1}[0](mul0r (J 0 li)) => /(mulIf hJ) <-.
Qed.

Lemma pcapr0 m n (I: 'rV[R]_m) : pcap I (0: 'rV[R]_n) = 0.
Proof.
rewrite /pcap.
case: find_nonzeroP => //= i hI.
set J := \row_j _.
suff : J = 0 by move => ->; rewrite /addid row_mx0.
apply/rowP => j; rewrite !mxE.
case: odivrP => //= a; rewrite /mulid.
case/mxvec_indexP : j => c r; rewrite mxvecE !mxE.
case/mxvec_indexP : c => l c.
rewrite big_ord_recl big_ord0 addr0 !mxE mxvecE !mxE.
rewrite big_ord_recl big_ord0 addr0 !mxE mulr0.
move: hI; rewrite !mxE.
case: splitP => li hli; last by rewrite !mxE eqxx.
move => hI.
by rewrite -{1}[0](mul0r (I 0 li)) => /(mulIf hI) <-.
Qed.

Lemma pcap_subidl m n (I: 'rV[R]_m) (J: 'rV[R]_n): (pcap I J <= I)%IS.
Proof.
case h0 : ((I +i J)%IS != 0); last first.
- move/negbT : h0; rewrite negbK => /eqP /rowP h0.
  have -> : I = 0.
  + apply/rowP => i.
    move: (h0 (lshift n i)); rewrite !mxE.
    case: splitP => ii /= hii.
      by have -> : i = ii by apply/ord_inj.
    case: (@destr ii m).
    by rewrite -hii.
  by rewrite pcap0r; apply/subidP; exists 0; rewrite mul0mx.
have h1 : (I *i J <= I *i (I +i J))%IS.
- apply/subid_mulid_congr; first by apply/subid_refl.
  apply/subidP; exists (col_mx 0 1%:M).
  by rewrite /addid mul_row_col mulmx0 add0r mulmx1.
case/andP : (pcap_id I J) => hl hr.
apply/(subid_mulidKl h0).
apply/(subid_trans _ (subid_mulC _ _)).
by apply/(subid_trans hl).
Qed.

Lemma pcap_subidr m n (I: 'rV[R]_m) (J: 'rV[R]_n): (pcap I J <= J)%IS.
Proof.
case h0 : ((I +i J)%IS != 0); last first.
- move/negbT : h0; rewrite negbK => /eqP /rowP h0.
  have -> : J = 0.
  + apply/rowP => i.
    move: (h0 (rshift m i)); rewrite !mxE.
    case: splitP => /= [ii hii | ii].
      case: (@destr i m).
      by rewrite hii.
    move/eqP; rewrite eqn_add2l => /eqP hii.
    by have -> : i = ii by apply/ord_inj.
  by rewrite pcapr0; apply/subidP; exists 0; rewrite mul0mx.
have h1 : (I *i J <= J *i (I +i J))%IS.
- apply/(subid_trans _ (subid_mulC _ _)).
- apply/subid_mulid_congr; last by apply/subid_refl.
  apply/subidP; exists (col_mx 1%:M 0).
  by rewrite /addid mul_row_col mulmx0 addr0 mulmx1.
case/andP : (pcap_id I J) => hl hr.
apply/(subid_mulidKl h0).
apply/(subid_trans _ (subid_mulC _ _)).
by apply/(subid_trans hl).
Qed.

Lemma pcap_member m n x (I : 'rV[R]_m) (J : 'rV[R]_n) :
  member x I -> member x J -> member x (pcap I J).
Proof.
move=> /member_subidP hA /member_subidP hB.
by apply/member_subidP/testF.
Qed.

Lemma pcap_spec m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  @int_spec _ _ m n I J (pcap I J).
Proof.
case/andP: (pcap_id I J) => h1 h2.
constructor.
- exact: pcap_subidl.
- exact: pcap_subidr.
by move=> x; apply: pcap_member.
Qed.

Lemma pcapP m n (I: 'rV[R]_m) (J: 'rV[R]_n) (x: R) :
  member x (pcap I J) <-> (member x I /\ member x J).
Proof.
case: pcap_spec => h1 h2 /= h3.
split => [h | [hl hr]]; last by apply/i.
by split; apply/(member_subid h).
Qed.

Lemma pcapC m n (I: 'rV[R]_m) (J: 'rV[R]_n) : (pcap I J == pcap J I)%IS.
Proof.
by apply/andP; split; apply/subid_memberP => /= x /pcapP [h1 h2]; apply/pcapP.
Qed.

(* It is possible to instantiate the coherent structure now but *)
(* we first want a version of ideal intersection that is more suitable *)
(* for computation *)
(* Definition prufer_coherentMixin := int_coherentMixin pcap_spec. *)
(* Canonical Structure prufer_coherentType := *)
(*   Eval hnf in CoherentRingType R prufer_coherentMixin. *)

(** A version of the intersection algorithms that is more suitable for
   computation because it use the predictable version of ideal multiplication  *)
Definition pcapc (m n: nat) (I : 'rV[R]_m) (J : 'rV[R]_n) :
  'rV[R]_(pcap_size I J).+1 := match find_nonzero (I +i J) with
  | Some i =>  let sIJ  := I +i J in
               let a    := sIJ 0 i in
               let acap := mulidc (mulidc (inv_id i sIJ) I) J in
               (0 : 'M_1) +i (\row_i (odflt 0 (acap 0 i %/? a)))
  | None => 0
  end.

Lemma pcapc_dvd m n (I: 'rV[R]_m) (J: 'rV[R]_n) i j :
  (I +i J) 0 i %| (mulidc (mulidc (inv_id i (I +i J)) I) J) 0 j.
Proof.
case: (mulidc_in_mulid2 (inv_id i (I +i J)) I J j) => k hk.
by move: (pcap_dvd I J i k); rewrite hk.
Qed.

Lemma pcapcP m n (I : 'rV[R]_m) (J : 'rV[R]_n) : (pcap I J == pcapc I J)%IS.
Proof.
rewrite /pcap /pcapc.
case: find_nonzeroP; last first.
  by move=> _; apply/andP; split; apply/subidP; exists 0; rewrite mulmx0.
move=> i hi.
set R1 := \row__ _.
set R2 := \row__ _.
suff h : (R1 == R2)%IS.
  apply/andP.
  by split; apply/(@addid_congr _ 1 _ 1); rewrite ?subid_refl //; case/andP: h.
have H : (mulidc (mulidc (inv_id i (I +i J)) I) J ==
          ((inv_id i (I +i J) *i I) *i J))%IS.
  move: (mulidcP (mulidc (inv_id i (I +i J)) I) J); rewrite eqid_sym => h.
  apply/(eqid_trans h)/mulid_congr; last by apply/eqid_refl.
  by rewrite eqid_sym mulidcP.
rewrite (eqid_scaleid _ _ hi) /R1 /R2 -!mul_scalar_mx.
set sIJ  := I +i J.
set a    := sIJ 0 i.
set acap := inv_id i sIJ *i I *i J.
set acap' := mulidc _ _.
have -> : (a%:M *m \row_i odflt 0 (acap 0 i %/? a)) = acap.
  apply/rowP=>j.
  rewrite !mxE big_ord1 !mxE eqxx mulr1n.
  case: odivrP => /= [x|]; first by rewrite mulrC => <-.
  case/dvdrP: (pcap_dvd I J i j)=> x hx /(_ x).
  by rewrite hx eqxx.
have -> : (a%:M *m \row_i odflt 0 (acap' 0 i %/? a)) = acap'.
  apply/rowP=>j.
  rewrite !mxE big_ord1 !mxE eqxx mulr1n.
  case: odivrP => /= [x|]; first by rewrite mulrC => <-.
  case/dvdrP: (pcapc_dvd I J i j)=> x hx /(_ x).
  by rewrite hx eqxx.
case/andP: H => /subidP [X hX] /subidP [Y hY].
apply/andP; split; apply/subidP.
  exists Y.
  apply/rowP=> j.
  move/rowP: hY => /(_ j).
  by rewrite !mxE => ->.
exists X.
apply/rowP=> j.
move/rowP: hX => /(_ j).
by rewrite !mxE => ->.
Qed.

Lemma pcapc_spec m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  @int_spec _ _ m n I J (pcapc I J).
Proof.
move: (pcap_subidl I J) (pcap_subidr I J) => h1 h2.
case/andP: (pcapcP I J) => g h.
constructor => /=.
- exact: (subid_trans h h1).
- exact: (subid_trans h h2).
move=> x hI hJ.
have ha: member x I /\ member x J by split.
case: (pcapP I J x) => _ /(_ ha) /member_subidP hx.
apply/member_subidP.
exact: (subid_trans hx g).
Qed.

Definition prufer_coherentMixin := int_coherentMixin pcap_spec.
Canonical Structure bezout_coherentType :=
  Eval hnf in CoherentRingType R prufer_coherentMixin.

End Coherent.