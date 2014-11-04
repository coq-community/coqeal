Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Require Import ssralg fintype perm choice.
Require Import matrix bigop zmodp mxalgebra poly.

Require Import cssralg dvdring cdvdring ssrcomplements seqmatrix.
Require Import stronglydiscrete cstronglydiscrete coherent ccoherent prufer.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(** Computable Prufer domain *)
Module CPruferDomain.

Record mixin_of (R : pruferDomainType) (CR : cdvdRingType R) : Type := Mixin {
  cprufer : CR -> CR -> (CR * CR * CR)%type;
  _ : forall x y,
      let: (cu,cv,cw) := cprufer (trans x) (trans y) in
      let: (u,v,w)    := prufer x y in
      [/\ trans u == cu, trans v == cv & trans w == cw]
}.

Section ClassDef.

Variable R : pruferDomainType.
Implicit Type phR : phant R.

Structure class_of (V : Type) := Class {
  base  : CDvdRing.class_of R V;
  mixin : mixin_of (CDvdRing.Pack _ base V)
}.

Local Coercion base : class_of >-> CDvdRing.class_of.

Structure type phR : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):= let: Pack _ c _ := cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.
Definition pack phR T V0 (m0 : mixin_of (@CDvdRing.Pack R _ T V0 T)) :=
  fun bT b & phant_id (@CDvdRing.class _ phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition czmodType phR cT := CZmodule.Pack phR (@class phR cT) cT.
Definition cringType phR cT := CRing.Pack phR (@class phR cT) cT.
Definition cDvdRingType phR cT := CDvdRing.Pack phR (@class phR cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> CDvdRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >-> Equality.type.
Canonical Structure eqType.
Coercion czmodType: type >-> CZmodule.type.
Canonical Structure czmodType.
Coercion cringType: type >-> CRing.type.
Canonical Structure cringType.
Coercion cDvdRingType: type >-> CDvdRing.type.
Canonical Structure cDvdRingType.

Notation cpruferDomainType R  := (@type _ (Phant R)).
Notation CPruferDomainType R m := (@pack _ (Phant R) _ _ m _ _ id _ id).
Notation CPruferDomainMixin := Mixin.
Notation "[ 'cpruferDomainType' T 'of' V 'for' cT ]" := (@clone _ (Phant V) T cT _ idfun)
  (at level 0, format "[ 'cpruferDomainType' T 'of'  V  'for'  cT ]") : form_scope.
Notation "[ 'cpruferDomainType' T 'of' V ]" := (@clone _ (Phant V) T _ _ id)
  (at level 0, format "[ 'cpruferDomainType' T 'of' V ]") : form_scope.
End Exports.

End CPruferDomain.

Export CPruferDomain.Exports.

Definition cprufer (R : pruferDomainType) (CR : cpruferDomainType R) :=
  CPruferDomain.cprufer (CPruferDomain.class CR).

Section CPruferDomainTheory.

Variable R : pruferDomainType.
Variable CR : cpruferDomainType R.

Lemma cpruferE : forall (x y : R),
      let: (cu,cv,cw) := cprufer (@trans _ CR x) (trans y) in
      let: (u,v,w)    := prufer x y in
      [/\ trans u == cu, trans v == cv & trans w == cw].
Proof. by case: CR => [? [? []]]. Qed.

Definition cpruferAlt (x y : CR) : CR * CR * CR * CR:=
  let: (u,v,w) := cprufer x y in (u,v,w,sub (one CR) u).

Lemma cpruferAltE x y :
  let: (cu,cv,cw,cu') := cpruferAlt (@trans _ CR x) (trans y) in
  let: (u,v,w,u')     := pruferAlt x y in
  [/\ trans u == cu, trans v == cv, trans w == cw & trans u' == cu'].
Proof.
move: (cpruferE x y).
rewrite /cpruferAlt /pruferAlt.
case: cprufer => [[a' b'] c']; case: prufer => [[a b] c].
by rewrite subE oneE => [[/eqP -> -> ->]].
Qed.

(** Some lemmas about foldr and big_sum *)
Lemma trans_foldr n (f : 'I_n -> R) (x : R) : forall xs,
  trans (foldr (fun i : 'I_n => [eta +%R (f i)]) x xs) =
  foldr (fun i => [eta add (trans (f i))]) (@trans R CR x) xs.
Proof. by elim=> //= a xs ih; rewrite addE ih. Qed.

Lemma foldr_eq n (f1 f2 : 'I_n.+1 -> CR -> CR) x xs (h : f1 =2 f2) :
  foldr f1 x xs = foldr f2 x xs.
Proof. by elim: xs => //= a xs ->; rewrite h. Qed.

Definition big_sum (n : nat) (f : 'I_n -> CR) :=
  foldr (fun i x => add (f i) x) (zero CR) (ord_enum_eq n).

Lemma big_sumE n f :
  trans (\big[+%R/0]_(i < n) (f i)) = @big_sum n (fun x => trans (f x)).
Proof.
rewrite /big_sum unlock /= /reducebig trans_foldr zeroE ord_enum_eqE.
by rewrite /index_enum -enumT.
Qed.

(* (* This was nice but never needed: *)
Lemma trans_foldr f (x : R) : forall xs,
  trans (foldr (fun i : nat => [eta +%R (f i)]) x xs) =
  foldr (fun i => [eta add (trans (f i))]) (@trans R CR x) xs.
Proof. by elim=> //= a xs ih; rewrite addE ih. Qed.

Definition big_sum (m n : nat) f :=
  foldr (fun i x => add (f i) x) (zero CR) (iota m (n - m)).

Lemma big_sumE (m n : nat) (f : nat -> R) :
  trans (\big[+%R/0]_(m <= i < n) (f i)) = big_sum m n (fun x => trans (f x)).
Proof.
by rewrite /big_sum unlock /= /reducebig /index_iota trans_foldr zeroE.
Qed.

Definition big_sum0 (n : nat) f :=
  foldr (fun i x => add (f i) x) (zero CR) (iota 0 n).

Lemma big_sum0E (n : nat) (f : nat -> R) :
  trans (\big[+%R/0]_(i < n) (f i)) = big_sum0 n (fun x => trans (f x)).
Proof.
move: (big_sumE 0 n f); rewrite /big_sum0 /big_sum subn0 => <-.
elim: n=> [|n ih]; first by rewrite big_ord0 big_geq.
by rewrite big_ord_recr addE ih -addE; rewrite big_nat_recr.
Qed.
*)

Fixpoint cplm m (M : seqmatrix CR) : seqmatrix CR :=
  if m == 1%N then seqmx1 CR 1 else match m with
    | S p =>
      let: u := fun i => (cpruferAlt (M O O) (M O i.+1)).1.1.1 in
      let: v := fun i => (cpruferAlt (M O O) (M O i.+1)).1.1.2 in
      let: w := fun i => (cpruferAlt (M O O) (M O i.+1)).1.2 in
      let: t := fun i => (cpruferAlt (M O O) (M O i.+1)).2 in
      let: B  := cplm p (rsubseqmx 1 M) in
        mkseqmx_ord (fun (i j : 'I_(1 + p)%N) =>
          match i == 0, j == 0 with
           | true, true => @big_sum p (fun k => mul (B k k) (t k))
           | true, false => @big_sum p (fun k => mul (B k j.-1) (w k))
           | false, true => mul (B i.-1 i.-1) (v i.-1)
           | false, false => mul (B i.-1 j.-1) (u i.-1)
           end)
    | O => seqmx1 CR 0
  end.

Lemma cplmE : forall n (M : 'rV[R]_n),
  cplm n (seqmx_of_mx CR M) = seqmx_of_mx CR (plm M).
Proof.
elim=> [M | /= n ih]; first by rewrite seqmx1E.
rewrite [n.+1]/(1 + n)%N => M.
move: (ih (rsubmx M)) => {ih}.
case: n M => [M _ | n M ih] /=; first by rewrite seqmx1E.
rewrite !seqmx_of_funE.
apply: eq_mkseqmx_ord => i j.
case: splitP => k hk; case: splitP=> l hl.
- have -> : i = 0 by apply/ord_inj; rewrite hk ord1.
  have -> : j = 0 by apply/ord_inj; rewrite hl ord1.
  rewrite eqxx big_sumE /big_sum.
  apply: foldr_eq=> p q.
  rewrite mulE (seqmxE _ _ 0 0) (seqmxE _ _ 0 (lift 0 p)).
  case: cpruferAlt (cpruferAltE (M 0 0) (M 0 (lift 0 p))) => [[[a b c d]]].
  case: pruferAlt  => [[[a' b' c' d']]] [_ _ _ /eqP ->].
  by rewrite -seqmxE -ih rsubseqmxE.
- have -> : i = 0 by apply/ord_inj; rewrite hk ord1.
  have -> : j = (rshift 1 l)%N by rewrite rshift1; apply/ord_inj.
  rewrite eqxx rshift1 lift0 /= big_sumE /big_sum.
  apply: foldr_eq => p q.
  rewrite mulE (seqmxE _ _ 0 0) (seqmxE _ _ 0 (lift 0 p)).
  case: cpruferAlt (cpruferAltE (M 0 0) (M 0 (lift 0 p))) => [[[a b c d]]].
  case: pruferAlt  => [[[a' b' c' d']]] [_ _ /eqP ->].
  by rewrite -seqmxE -ih rsubseqmxE.
- have -> : j = 0 by apply/ord_inj; rewrite hl ord1.
  have -> : i = (rshift 1 k)%N by rewrite rshift1; apply/ord_inj.
  rewrite eqxx rshift1 lift0 /= mulE (seqmxE _ _ 0 0) (seqmxE _ _ 0 (lift 0 k)).
  case: cpruferAlt (cpruferAltE (M 0 0) (M 0 (lift 0 k))) => [[[a b c d]]].
  case: pruferAlt => [[[a' b' c' d']]] [_  /eqP ->].
  by rewrite -seqmxE -ih rsubseqmxE.
have -> : i = (rshift 1 k)%N by rewrite rshift1; apply/ord_inj.
have -> : j = (rshift 1 l)%N by rewrite rshift1; apply/ord_inj.
rewrite rshift1 lift0 /= mulE (seqmxE _ _ 0 0) (seqmxE _ _ 0 (lift 0 k)).
case: cpruferAlt (cpruferAltE (M 0 0) (M 0 (lift 0 k))) => [[[a b c d]]].
case: pruferAlt => [[[a' b' c' d']]] [/eqP ->].
by rewrite -seqmxE -ih rsubseqmxE.
Qed.

Definition cinv_id n i (I : seqmatrix CR) := match n with
  | O   => seqmx0 CR 1 O
  | S p => trseqmx (colseqmx i (cplm n I))
  end.

Lemma cinv_idE : forall n (i : 'I_n) (I : 'rV[R]_n),
  cinv_id n i (seqmx_of_mx CR I) = seqmx_of_mx CR (inv_id i I).
Proof.
elim => [/= _ _| n ih i I]; first by rewrite seqmx0E.
by rewrite /cinv_id cplmE colseqmxE trseqmxE.
Qed.

End CPruferDomainTheory.

Section CStronglyDiscrete.

Variable R : pruferDomainType.
Variable CR : cpruferDomainType R.

Definition cpmember n (x : CR) (I : seqmatrix CR) : option (seqmatrix CR) :=
  match n with
  | S p =>
    let: loc := cplm n I in
    if all (fun (i : 'I_n) => cdvd (I O i) (mul (loc i i) x)) (ord_enum_eq n)
     then Some (mkseqmx_ord (fun (i : 'I_n) (j: 'I_1) =>
                             odflt (zero CR) (cdiv (mul (loc i i) x) (I O i))))
     else None
  | _ => if x == zero CR then Some (seqmx0 CR O O) else None
end.

Lemma cpmemberE : forall n x (I : 'rV[R]_n),
  omap trans (pmember x I) = cpmember n (trans x) (seqmx_of_mx CR I).
Proof.
elim => [x I|n ih x].
  by rewrite thinmx0 /= trans_eq0; case: ifP => //= _; rewrite zeroE.
rewrite [n.+1]/(1 + n)%N /cpmember => I.
have -> : pmember x I = if [forall i, I 0 i %| (plm I) i i * x] then
          Some (\col_i odflt 0 ((plm I) i i * x %/? I 0 i)) else None
          by [].
set C  : 'M[R]_(1 + n) := plm I.
set C' := cplm (1 + n)%N (seqmx_of_mx CR I).
set B := [forall i, _].
set B' := all _ _.
have -> : B = B'.
  rewrite /B /B'.
  apply/forallP/allP=> /= h i; move: (h i).
    by rewrite (seqmxE _ _ 0 i) /C' cplmE (seqmxE _ _ i i) -mulE -cdvdE.
  rewrite (@cdvdE _ CR) mulE /C -!seqmxE -cplmE; apply.
  by rewrite ord_enum_eqE enumT unlock /= mem_ord_enum.
case: ifP=> // _; rewrite /trans /= !seqmx_of_funE; congr (Some _).
apply: eq_mkseqmx_ord => i _ /=.
rewrite (seqmxE _ _ 0 i) /C' cplmE (seqmxE _ _ i i) -mulE -cdivE.
by case: odivrP => //= _; rewrite zeroE.
Qed.

Definition cprufer_cstronglyDiscreteMixin := CStronglyDiscrete.Mixin cpmemberE.
Canonical Structure cprufer_cstronglyDiscreteType :=
  Eval hnf in CStronglyDiscreteType R cprufer_cstronglyDiscreteMixin.

End CStronglyDiscrete.

Section CCoherent.

Variable R : pruferDomainType.
Variable CR : cpruferDomainType R.

Fixpoint cfind_nonzero n (I : seqmatrix CR) : option 'I_n := match n with
  | O => None
  | S p =>
    if I O O != zero CR
       then Some 0
       else omap (fun i => lift 0 i) (cfind_nonzero p (rsubseqmx 1 I))
  end.

Lemma cfind_nonzeroE : forall n (I : 'rV[R]_n),
  find_nonzero I = cfind_nonzero n (seqmx_of_mx CR I).
Proof.
elim => // n ih I /=.
rewrite (seqmxE _ _ 0 0) trans_eq0.
case: ifP => // h.
by rewrite ih rsubseqmxE.
Qed.

Definition cpcap_size (m n : nat) (I : seqmatrix CR) (J : seqmatrix CR) :=
  (((m + n) * m) * n)%N.

Definition cpcapc (m n : nat) (I : seqmatrix CR) (J : seqmatrix CR) :=
  match cfind_nonzero (m + n) (row_seqmx I J) with
  | Some i =>  let sIJ  := row_seqmx I J in
               let a    := sIJ O i in
               let acap : seqmatrix CR := cmulidc ((m + n) * m) n
                           (cmulidc (m + n) m (cinv_id (m + n) i sIJ) I) J in
              row_seqmx (seqmx0 CR 1 1)
                 (mkseqmx_ord (fun (i : 'I_1) (j: 'I_(cpcap_size m n I J)) =>
                 (odflt (zero CR) (cdiv (acap O (nat_of_ord j)) a))))
  | None => seqmx0 CR 1 (cpcap_size m n I J).+1
  end.

Lemma cpcapE m n (I : 'rV[R]_m) (J : 'rV[R]_n) :
  seqmx_of_mx CR (pcapc I J) = cpcapc m n (seqmx_of_mx CR I) (seqmx_of_mx CR J).
Proof.
rewrite /pcapc /cpcapc.
rewrite row_seqmxE.
rewrite -cfind_nonzeroE.
case: find_nonzeroP => [i hi|_]; last by rewrite seqmx0E.
rewrite -seqmx0E -[seqmx_of_mx CR (row_mx (0 : 'M_1) _)]row_seqmxE.
f_equal.
rewrite seqmx_of_funE.
apply: eq_mkseqmx_ord => j k /=.
rewrite cinv_idE !cmulidcE (seqmxE CR _ 0 i) (seqmxE CR _ 0 k) -cdivE.
by case: odivrP => //= _; rewrite zeroE.
Qed.

(* Definition prufer_coherentMixin := *)
(*   int_coherentMixin2 pcap_spec. *)
(* Canonical Structure bezout_coherentType := *)
(*   Eval hnf in CoherentRingType R prufer_coherentMixin. *)

End CCoherent.

Section CBezoutCPrufer.

Variable R : bezoutRingType.
Variable CR : cbezoutRingType R.

Definition cbezout_calc (x y : CR) : (CR * CR * CR)%type :=
  let: (g,c,d,a,b) := cegcdr x y in
    (mul d b, mul a d, mul b c).

Lemma cbezout_calcE (x y : R) :
  let: (u',v',w') := cbezout_calc (trans x) (trans y) in
  let: (u,v,w) := prufer x y in
  [/\ trans u == u', trans v == v' & trans w == w'].
Proof.
rewrite /prufer /= /bezout_calc /cbezout_calc.
case: egcdr (cegcdrE CR x y) => /= [[[[a b c d e]]]].
case: cegcdr => /= [[[[a' b' c' d' e']]]].
by rewrite !mulE => [[_ -> -> -> ->]].
Qed.

Definition cbezout_cpruferMixin :=
  CPruferDomainMixin cbezout_calcE.
Canonical Structure bezout_pruferType :=
  Eval hnf in CPruferDomainType R cbezout_cpruferMixin.

End CBezoutCPrufer.
