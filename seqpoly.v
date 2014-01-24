(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements polydiv.

(******************************************************************************)
(** This file implements dense polynomials as lists.                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op AlgOp.

(******************************************************************************)
(** PART I: Defining generic datastructures and programming with them         *)
(******************************************************************************)
Section seqpoly_op.

Variable T : Type.

Definition seqpoly := seq T.

Context `{zero T, one T, add T, sub T, opp T, mul T, eq T}.

Local Open Scope computable_scope.

Fixpoint zero_drop p : seqpoly := match p with
  | [::]    => [::]
  | x :: xs => if (x == 0)%C then zero_drop xs else x :: xs
  end.

(* Remove trailing zeroes *)
Definition drop_zero p : seqpoly := rev (zero_drop (rev p)).

Definition zippolywith R (f : T -> T -> R) :=
  let fix aux p q :=
      match p, q with
        | [::], q' => map (f 0) q
        | p', [::] => map (f^~ 0) p
        | a :: p', b :: q' => f a b :: (aux p' q')
      end in aux.

Global Instance zero_seqpoly : zero seqpoly := [::].
Global Instance one_seqpoly  : one seqpoly  := [:: 1].
Global Instance add_seqpoly  : add seqpoly  := zippolywith +%C.
Global Instance opp_seqpoly  : opp seqpoly  := map -%C.
Global Instance sub_seqpoly  : sub seqpoly  := zippolywith sub_op.

(* Is this a reasonable comparison operator, particularily when not equal? *)
Global Instance eq_seqpoly : eq seqpoly := fun p q =>
  all (eqtype.eq_op true) (zippolywith eq_op p q).

Global Instance scale_seqpoly : scale T seqpoly := fun a => map ( *%C a).

(* shifting = * 'X^n, maybe we should parametrize by an implem of nat? *)
Definition shift (n : nat) : seqpoly -> seqpoly := ncons n 0%C.
Arguments shift n p : simpl nomatch.

(* size of the polynomial, parametrize by implem of nat? *)
Definition size_seqpoly : seqpoly -> nat :=
  let fix aux p :=
      if p is a :: p then
        let sp := aux p in
        if sp == 0%N then ~~ (a == 0)%C : nat else sp.+1
      else 0%N in aux.

(* Definition size_seqpoly : seqpoly -> nat := size \o drop_zero. *)

(* leading coefficient of the polynomial *)
Definition lead_coef_seqpoly (sp : seqpoly) : T :=
  nth 0 sp (size_seqpoly sp).-1.

(* More efficient version that only require one go through the list *)
(* Definition lead_coef_seqpoly : seqpoly -> T := *)
(*   let fix aux x p := *)
(*       if p is a :: p then  *)
(*          if (a == 0)%C then aux x p else aux a p *)
(*       else x in aux 0. *)

(* polyC *)
Global Instance embed_seqpoly : cast_class T seqpoly :=
  fun a => nseq (~~ (a == 0)%C) a.

(* Spliting a polynomial, useful for Karatsuba *)
Definition split_seqpoly n (p : seqpoly) := (drop n p, take n p).

(* multiplication *)
Global Instance mul_seqpoly : mul seqpoly := fun p q =>
  let fix aux p :=
      if p is a :: p then (a *: q + shift 1%N (aux p))%C else 0
  in aux p.

(* Horner evaluation *)
Fixpoint horner_seq (s : seqpoly) x :=
  if s is a :: s' then (horner_seq s' x * x + a)%C else 0.

(* pseudo-division *)
Definition edivp_rec_seqpoly (q : seqpoly) :=
  let sq := size_seqpoly q in
  let cq := cast (lead_coef_seqpoly q) in
  fix loop (k : nat) (qq r : seqpoly) (n : nat) {struct n} :=
    if (size_seqpoly r < sq)%N then (k, qq, r) else
    let m := shift (size_seqpoly r - sq) (cast (lead_coef_seqpoly r)) in
    let qq1 := (qq * cq + m)%C in
    let r1 := (r * cq - m * q)%C in
    if n is n1.+1 then loop k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

Definition divp_seqpoly p q  :=
  (if (q == 0)%C then (0%N, 0%C, p)
                 else edivp_rec_seqpoly q 0 0%C p (size_seqpoly p)).1.2.
Definition modp_seqpoly p q  :=
  (if (q == 0)%C then (0%N, 0%C, p)
                 else edivp_rec_seqpoly q 0 0%C p (size_seqpoly p)).2.
Definition scalp_seqpoly p q :=
  (if (q == 0)%C then (0%N, 0%C, p)
                 else edivp_rec_seqpoly q 0 0%C p (size_seqpoly p)).1.1.

End seqpoly_op.

(******************************************************************************)
(** PART II: Proving correctness properties of the previously defined objects *)
(******************************************************************************)
Section seqpoly_theory.

Variable R : ringType.

Instance zeroR : zero R := 0%R.
Instance oneR  : one R  := 1%R.
Instance addR  : add R  := +%R.
Instance oppR  : opp R  := -%R.
Instance subR  : sub R  := subr.
Instance mulR  : mul R  := *%R.
Instance eqR   : eq R   := eqtype.eq_op.

Lemma seqpoly_of_polyK : pcancel (@polyseq R) (some \o Poly).
Proof. by move=> p /=; rewrite polyseqK. Qed.

Definition Rseqpoly : {poly R} -> seqpoly R -> Prop := fun_hrel Poly.

Lemma RpolyE p q : param Rseqpoly p q -> p = Poly q.
Proof. by rewrite paramE. Qed.

(* zero and one *)
Instance Rseqpoly_0 : param Rseqpoly 0%R 0%C.
Proof. by rewrite paramE. Qed.

Instance Rseqpoly_1 : param Rseqpoly 1%R 1%C.
Proof. by rewrite paramE /Rseqpoly /fun_hrel /= cons_poly_def mul0r add0r. Qed.

Instance Rseqpoly_cons : param (Logic.eq ==> Rseqpoly ==> Rseqpoly)
  (@cons_poly R) (@cons R).
Proof.
rewrite paramE => /= b a -> {b} p s ps.
by apply/polyP => i /=; rewrite [p]RpolyE cons_poly_def.
Qed.

(* drop_zero *)
Lemma Poly_rcons0 : forall (s : seq R), Poly (rcons s 0) = Poly s.
Proof. by elim=> /= [|a s ->] //; rewrite cons_poly_def mul0r add0r. Qed.

Definition drop0p := @idfun {poly R}.

Instance Rseqpoly_drop_zero :
  param (Rseqpoly ==> Rseqpoly) drop0p (@drop_zero _ _ _).
Proof.
rewrite paramE => _ sp <-.
elim/last_ind: sp => //= s a.
rewrite /drop_zero rev_rcons /=; simpC => ih.
have [->|_] := (altP eqP); last by rewrite rev_cons revK.
by rewrite Poly_rcons0.
Qed.

(* zippolywith *)
Lemma zippolywithE S (f : R -> R -> S) (p q : seqpoly R) :
  zippolywith f p q = mkseq (fun i => f (nth 0 p i) (nth 0 q i))
                            (maxn (size p) (size q)).
Proof.
have sz : size (zippolywith f p q) = (maxn (size p) (size q)) => [z|].
  elim: p q => [|a p ihp] [|b q] //=; do ?by rewrite size_map ?maxn0.
  by rewrite ihp maxnSS.
case hz: zippolywith sz => [|z s] /(_ zeroR); first by rewrite hz => <-.
rewrite -hz => {hz} sz.
apply: (@eq_from_nth _ z); first by rewrite size_mkseq sz.
move=> i; rewrite sz => hi; rewrite nth_mkseq // => {sz}.
elim: p q i hi => [|a p ihp] [|b q] [|i] //=;
rewrite ?nth_nil (maxn0, max0n, maxnSS) ltnS => hi; rewrite ?(nth_map 0) //.
by rewrite ihp.
Qed.

(* negation *)
Instance Rseqpoly_opp : param (Rseqpoly ==> Rseqpoly) -%R -%C.
Proof.
rewrite paramE => /= x a xa.
apply/polyP => i /=; rewrite /opp_op /opp_seqpoly /=.
rewrite [x]RpolyE coef_opp_poly !coef_Poly.
have [hlt|hleq] := ltnP i (size a); first by rewrite (nth_map 0%C).
by rewrite !nth_default ?oppr0 ?size_mkseq ?size_map.
Qed.

(* addition *)
Instance Rseqpoly_add : param (Rseqpoly ==> Rseqpoly ==> Rseqpoly) +%R +%C.
Proof.
rewrite paramE => /= x a xa y b yb; apply/polyP => i.
rewrite /add_op /add_seqpoly /= zippolywithE [x]RpolyE [y]RpolyE /= coef_Poly.
have [i_small|i_large] := ltnP i (maxn (size a) (size b)).
  by rewrite nth_mkseq // coef_add_poly //= !coef_Poly.
rewrite !nth_default // ?size_mkseq //.
rewrite (leq_trans (leq_trans (size_add _ _) _) i_large) //.
by rewrite geq_max !leq_max !size_Poly orbT.
Qed.

(* subtraction *)
Instance Rseqpoly_sub : param (Rseqpoly ==> Rseqpoly ==> Rseqpoly) subr sub_op.
Proof.
rewrite paramE => /= x a xa y b yb.
apply/polyP => i; rewrite /sub_op /sub_seqpoly /= zippolywithE.
rewrite [x]RpolyE [y]RpolyE /= coef_Poly.
have [i_small|i_large] := ltnP i (maxn (size a) (size b)).
  by rewrite nth_mkseq // coef_add_poly //= coef_opp_poly !coef_Poly.
rewrite !nth_default // ?size_mkseq //.
rewrite (leq_trans (leq_trans (size_add _ _) _) i_large) //.
by rewrite size_opp geq_max !leq_max !size_Poly orbT.
Qed.

(* splitting *)
Definition splitp n (p : {poly R}) := (rdivp p 'X^n, rmodp p 'X^n).

Instance Rseqpoly_split : param (Logic.eq ==> Rseqpoly ==> Rseqpoly * Rseqpoly)
  splitp (@split_seqpoly R).
Proof.
rewrite paramE=> m n -> {m} p q <- {p}.
rewrite /Rseqpoly /fun_hrel /prod_hrel /=; apply/pair_andP.
elim: q n => //= [|b q ihq] [|n]; do ?by rewrite ?(rdiv0p, rmod0p).
  by rewrite //= cons_poly_def expr0 ?(rdivp1, rmodp1).
rewrite /= !cons_poly_def [Poly q](@rdivp_eq _ 'X^n) ?monicXn //.
have [-> ->] := ihq n; rewrite mulrDl -mulrA -exprSr -addrA.
suff htnq: size (rmodp (Poly q) 'X^n * 'X + b%:P) < size ('X^n.+1 : {poly R}).
  by rewrite rdivp_addl_mul_small ?rmodp_addl_mul_small ?monicXn //.
rewrite size_polyXn size_MXaddC ltnS; case: ifP => // _.
by rewrite (leq_trans (ltn_rmodpN0 _ _)) ?monic_neq0 ?monicXn ?size_polyXn.
Qed.

(* scaling *)
Instance Rseqpoly_scale : param (Logic.eq ==> Rseqpoly ==> Rseqpoly) *:%R *:%C.
Proof.
rewrite paramE => /= a b -> {a} p s ps.
apply/polyP => i /=; rewrite [p]RpolyE coefZ !coef_Poly.
have [hlt|hleq] := ltnP i (size s); first by rewrite (nth_map 0%C).
by rewrite !nth_default ?mulr0 ?size_mkseq ?size_map.
Qed.

(* This needs to be added to be able to use the instance below *)
Definition shiftp n (p : {poly R}) := p * 'X^n.

(* shifting = * 'X^n *)
Instance Rseqpoly_shift : param (Logic.eq ==> Rseqpoly ==> Rseqpoly)
  shiftp (@shift _ _).
Proof.
rewrite paramE => /= m n -> {m} p s ps.
by apply/polyP => i /=; rewrite [p]RpolyE coefMXn !coef_Poly nth_ncons.
Qed.

(* maybe this should be "all (fun x => x == 0) s" ? *)
Lemma Rseqpoly_poly0 (s : seqpoly R) : param Rseqpoly 0 s ->
  forall x, x \in s -> x = 0.
Proof.
by move=> hs x /(nthP 0) [i hi <-]; rewrite -coef_Poly -(RpolyE hs) coef0.
Qed.

Lemma Rseqpoly_MXaddC a p (s : seqpoly R) :
  param Rseqpoly (p * 'X + a%:P) s ->
  param Rseqpoly p (behead s) /\ a = head 0 s.
Proof.
wlog -> : s / s = (head 0 s) :: (behead s) => [hwlog|].
  case: s => [rp|x s]; last by apply: hwlog.
  have /= := hwlog [::0] erefl; rewrite [_ + _]RpolyE /= => H; apply H.
  by rewrite paramE; apply/polyP=> i /=; rewrite cons_poly_def mul0r addr0.
rewrite paramE /Rseqpoly /fun_hrel /= cons_poly_def => hp.
have := congr1 (fun p => some (rdivp p 'X)) hp.
have := congr1 (fun p => (rmodp p 'X)) hp.
rewrite ?(rdivp_addl_mul_small, rmodp_addl_mul_small);
  do ?by rewrite ?monicX ?size_polyC ?size_polyX ?ltnS ?leq_b1.
by move/polyC_inj => -> [] ->.
Qed.

Lemma Rseqpoly_poly0_cons a s : Rseqpoly 0 (a :: s) -> (Rseqpoly 0 s /\ a = 0).
Proof.
have {1}-> : 0 = 0 * 'X + 0%:P :> {poly R} by rewrite mul0r addr0.
by rewrite -[Rseqpoly]paramE; move/Rseqpoly_MXaddC => [? ->].
Qed.

Lemma Rseqpoly_poly_cons p x s : Rseqpoly p (x :: s) ->
  {pa | [/\ p = pa.1 * 'X + pa.2%:P, pa.2 = x & Rseqpoly pa.1 s]}.
Proof.
elim/poly_ind: p => [|p a ihp] in s *.
  by move=> /Rseqpoly_poly0_cons [rs ->]; exists 0; rewrite mul0r add0r.
rewrite -[Rseqpoly]paramE.
by move=> /Rseqpoly_MXaddC /= [rps ->]; exists (p, x).
Qed.

(* size *)
(* This definition hides the coercion which makes it possible for proof search
   to find Rseqpoly_seqpoly_size *)
Definition sizep : {poly R} -> nat := size.
Lemma sizepE s : sizep s = size s. Proof. by []. Qed.

Instance Rseqpoly_size :
  param (Rseqpoly ==> Logic.eq) sizep (@size_seqpoly _ _ _).
Proof.
rewrite paramE => p s ps; rewrite sizepE.
elim: s => [|x sp ihs] //= in p ps *; first by rewrite [p]RpolyE size_poly0.
move: ps => /Rseqpoly_poly_cons [[p' a /= [-> -> rp']]].
rewrite -(ihs p' rp') size_poly_eq0 size_MXaddC; simpC.
by have [->|] //= := (altP eqP); case: ifP => //=; rewrite size_poly0.
Qed.

(* lead_coef *)
Instance Rseqpoly_lead_coef :
  param (Rseqpoly ==> Logic.eq) lead_coef (fun p => lead_coef_seqpoly p).
Proof.
rewrite paramE /lead_coef_seqpoly /lead_coef => p s ps.
by rewrite -[size_seqpoly _]param_eq [p]RpolyE coef_Poly sizepE.
Qed.

(* polyC *)
Instance Rseqpoly_polyC :
  param (Logic.eq ==> Rseqpoly) (fun a => a%:P) (fun a => cast a)%C.
Proof.
rewrite paramE /cast /embed_seqpoly => b a -> {b}; simpC.
have [->|_] //= := (altP eqP);
by apply/polyP=> i /=; rewrite cons_poly_def mul0r add0r.
Qed.

(* multiplication *)
Instance Rseqpoly_mul : param (Rseqpoly ==> Rseqpoly ==> Rseqpoly) *%R *%C.
Proof.
apply param_abstr2 => /= p sp rp q sq rq.
elim: sp => [|a sp ihp] in p rp *; first by rewrite paramE [p]RpolyE mul0r.
move: rp; rewrite !paramE => /Rseqpoly_poly_cons [[sp' a'] /= [-> ra rp']].
rewrite mulrDl addrC mul_polyC -mulrA !(commr_polyX,mulrA) -mulrA.
rewrite /mul_op /= -commr_polyX -[0 :: _]/(shift 1%N _) -[_ * 'X]/(shiftp 1 _).
exact: paramP.
Qed.

(* equality *)
Instance Rseqpoly_eq : param (Rseqpoly ==> Rseqpoly ==> Logic.eq)
  (fun p q => p == q) (fun sp sq => sp == sq)%C.
Proof.
rewrite paramE => p sp hsp q sq hsq.
rewrite /eq_op /eq_seqpoly zippolywithE [p]RpolyE [q]RpolyE.
apply/eqP/idP => [hpq|/allP hpq].
  apply/allP => x /(nthP true) [i]; rewrite size_mkseq => hi <-.
  by rewrite nth_mkseq // eq_sym -coef_Poly hpq coef_Poly [(_ == _)%C]eqxx.
apply/polyP => i; rewrite !coef_Poly; apply/eqP.
set m := maxn _ _ in hpq; have [ge_im|lt_im] := leqP m i.
  by rewrite !nth_default // (leq_trans _ ge_im) // leq_max leqnn ?orbT.
rewrite -[_ == _](eqP (hpq _ _)) //; apply/(nthP true); rewrite size_mkseq.
by exists i => //; rewrite nth_mkseq.
Qed.

(* horner evaluation *)
Instance Rseqpoly_horner : param (Rseqpoly ==> Logic.eq ==> Logic.eq)
  (fun p x => p.[x]) (fun sp x => horner_seq sp x).
Proof.
rewrite paramE => p sp hsp x' x -> {x'}.
elim: sp => [|a sp ih] //= in p hsp *; first by rewrite [p]RpolyE /= horner0.
move: hsp => /Rseqpoly_poly_cons [[p' b /= [-> -> rp']]].
by rewrite -cons_poly_def horner_cons (ih _ rp').
Qed.

(* pseudo-division *)
Local Instance param_eq_refl A (n : A) : param Logic.eq n n | 999.
Proof. by rewrite paramE. Qed.

Instance Rseqpoly_edivp_rec :
  param (Rseqpoly ==> Logic.eq ==> Rseqpoly ==> Rseqpoly ==> Logic.eq ==>
         Logic.eq * Rseqpoly * Rseqpoly)
         (@redivp_rec R) (@edivp_rec_seqpoly _ _ _ _ _ _).
Proof.
rewrite paramE=> q sq hsq n m <- {m} p sp hsp r sr hsr m m' <- {m'} /=.
apply paramP; elim: m => [|m ih] /= in n p sp hsp q sq hsq r sr hsr *;
rewrite -![size_seqpoly _]param_eq -!sizepE -mul_polyC
        -[_ * 'X^_]/(shiftp (sizep r - sizep q) _) -[_ - _]/(subr _ _).
  by case: ifP=> // _; rewrite paramE; apply: paramP.
case: ifP=> // _; first by rewrite paramE.
by apply: ih=> //; apply: paramP.
Qed.

Instance Rseqpoly_divp : param (Rseqpoly ==> Rseqpoly ==> Rseqpoly)
  (@rdivp R) (fun p => divp_seqpoly p).
Proof.
apply param_abstr2; rewrite /rdivp unlock /divp_seqpoly /= => p sp hsp q sq hsq.
rewrite -sizepE -[(sq == 0)%C]param_eq; case: ifP=> _ /=; rewrite paramE //.
exact: paramP.
Qed.

Instance Rseqpoly_modp : param (Rseqpoly ==> Rseqpoly ==> Rseqpoly)
  (@rmodp R) (fun p => modp_seqpoly p).
Proof.
apply param_abstr2; rewrite /rmodp unlock /modp_seqpoly /= => p sp hsp q sq hsq.
rewrite -[(sq == 0)%C]param_eq; case: ifP=> _ //; rewrite -sizepE paramE.
exact: paramP.
Qed.

Instance Rseqpoly_scalp : param (Rseqpoly ==> Rseqpoly ==> Logic.eq)
  (@rscalp R) (fun p => scalp_seqpoly p).
Proof.
apply param_abstr2; rewrite /rscalp unlock /scalp_seqpoly => p sp hsp q sq hsq.
rewrite -sizepE -[(sq == 0)%C]param_eq; case: ifP=> _ /=; rewrite paramE //.
exact: paramP.
Qed.

(*************************************************************************)
(* PART III: Parametricity part                                          *)
(*************************************************************************)
Section seqpoly_parametricity.

Lemma param_zippolywith
  {A B : Type} (rAB : A -> B -> Prop)
  {C D : Type} (rCD : C -> D -> Prop)
  {zA : zero A} {zB : zero B} `{!param rAB zA zB} :
  (getparam (rAB ==> rAB ==> rCD) ==>
   getparam (seq_hrel rAB) ==> getparam (seq_hrel rAB) ==>
   getparam (seq_hrel rCD))%rel
  (@zippolywith A zA C) (@zippolywith B zB D).
Proof.
move: param0; rewrite !paramE => r f g rfg.
elim=> [[] //= _ s t rst|c cs ih1 [] //= d ds [r1 r2]].
  elim: s t rst => [[]|a l1 ih] // [|b l2] //= [r1 r2].
  split; [exact: rfg| exact: ih].
case=> //= [|s ss] [_|] //.
  split=> {ih1}; first by exact: rfg.
  elim: cs ds r2 => [[]|] // a l ih [] //= b s [r2 r3].
  split; [exact: rfg|exact: ih].
move=> t ts [r3 r4]; split; [exact: rfg | exact: ih1].
Qed.

Arguments param_zippolywith {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Hint Extern 1 (getparam _ _ _) =>
  eapply param_zippolywith : typeclass_instances.

Context (C : Type) (rAC : R -> C -> Prop).
Context `{zero C, one C, opp C, add C, sub C, mul C, eq C}.
Context `{!param rAC 0%R 0%C, !param rAC 1%R 1%C}.
Context `{!param (rAC ==> rAC) -%R -%C}.
Context `{!param (rAC ==> rAC ==> rAC) +%R +%C}.
Context `{!param (rAC ==> rAC ==> rAC) subr sub_op}.
Context `{!param (rAC ==> rAC ==> rAC) *%R *%C}.
Context `{!param (rAC ==> rAC ==> Logic.eq) eqtype.eq_op eq_op}.

Definition RseqpolyC := (Rseqpoly \o seq_hrel rAC)%rel.

Global Instance RseqpolyC_0 : param RseqpolyC 0%R 0%C.
Proof. exact: param_trans. Qed.

Global Instance RseqpolyC_1 : param RseqpolyC 1%R 1%C.
Proof. exact: param_trans. Qed.

Global Instance RseqpolyC_opp :
  param (RseqpolyC ==> RseqpolyC) -%R -%C.
Proof. exact: param_trans. Qed.

Global Instance RseqpolyC_add :
  param (RseqpolyC ==> RseqpolyC ==> RseqpolyC) +%R +%C.
Proof. exact: param_trans. Qed.

Global Instance RseqpolyC_sub :
  param (RseqpolyC ==> RseqpolyC ==> RseqpolyC) subr sub_op.
Proof. exact: param_trans. Qed.

Global Instance RseqpolyC_scale :
  param (rAC ==> RseqpolyC ==> RseqpolyC) *:%R *:%C.
Proof. exact: param_trans. Qed.

Global Instance RseqpolyC_shift : param (Logic.eq ==> RseqpolyC ==> RseqpolyC)
  (fun n p => p * 'X^n) (fun n => shift n).
Proof. exact: param_trans. Qed.

(* Global Instance RseqpolyC_size_seqpoly : param (RseqpolyC ==> Logic.eq) *)
(*   (fun (p : {poly R}) => size p) (fun s => size_seqpoly s). *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance RseqpolyC_lead_coef_seqpoly : *)
(*   param (RseqpolyC ==> rAC) lead_coef (fun p => lead_coef_seqpoly p). *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance RseqpolyC_polyC_seqpoly : *)
(*   param (rAC ==> RseqpolyC) (fun a => a%:P) (fun a => cast a)%C. *)
(* Proof. exact: param_trans. Qed. *)

(* Global Instance RseqpolyC_mul_seqpoly :  *)
(*   param (RseqpolyC ==> RseqpolyC ==> RseqpolyC) *%R *%C. *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance RseqpolyC_eq_seqpoly : param (RseqpolyC ==> RseqpolyC ==> Logic.eq)  *)
(*   (fun p q => p == q) (fun sp sq => sp == sq)%C. *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

(* Global Instance RseqpolyC_horner_seqpoly : param (RseqpolyC ==> rAC ==> rAC)  *)
(*   (fun p x => p.[x]) (fun sp x => horner_seq sp x). *)
(* Proof. admit. Qed. *)
(* (* Proof. exact: param_trans. Qed. *) *)

End seqpoly_parametricity.
End seqpoly_theory.

(* This does not work as seqpoly is not using parametricity yet! *)
(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0 + 0)%C : seqpoly Z. *)
(* Eval compute in (1 + 1)%C : seqpoly Z. *)
(* Eval compute in 1%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1)%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1 + 1 + 1 + 1)%C : *)
(*   seqpoly (seqpoly (seqpoly (seqpoly (seqpoly Z)))). *)
