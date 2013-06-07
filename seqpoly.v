(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements polydiv.

(******************************************************************************)
(* Lists (seq) is a refinement of SSReflect polynomials (poly)                *) 
(*                                                                            *)
(* Supported operations: 0, 1, +, -, scale, shift, *, ==, size, split + more...  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import GRing.Theory Pdiv.Ring  Pdiv.CommonRing Pdiv.RingMonic Refinements.Op. 

(*************************************************************)
(* PART I: Defining datastructures and programming with them *)
(*************************************************************)
Section seqpoly.

Variable T : Type.

Definition seqpoly := seq T.

Section seqpoly_ops.
Context `{zero T, one T, add T, sub T, opp T, mul T, eq T}.

Fixpoint zero_drop p : seqpoly := match p with
  | [::]    => [::]
  | x :: xs => if (x == 0)%C then zero_drop xs else x :: xs
  end.

Definition drop_zero p : seqpoly := rev (zero_drop (rev p)).

Definition zippolywith R (f : T -> T -> R) :=
  let fix aux p q :=
      match p, q with
        | [::], q' => map (f 0%C) q
        | p', [::] => map (f^~ 0%C) p
        | a :: p', b :: q' => f a b :: (aux p' q')
      end in aux.

Global Instance zero_seqpoly : zero seqpoly := [::].
Global Instance one_seqpoly  : one seqpoly  := [:: 1%C].
Global Instance add_seqpoly  : add seqpoly  := zippolywith +%C.
Global Instance opp_seqpoly  : opp seqpoly  := map -%C.
Global Instance sub_seqpoly  : sub seqpoly  := zippolywith sub_op.

(* is it a reasonnable comparison operator, particlarily when not equal? *)
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
        if sp == 0%N then ~~ (a == 0)%C else sp.+1
      else 0%N in aux.

(* leading coefficient of the polynomial *)
Definition lead_coef_seqpoly (sp : seqpoly) : T := 
  nth 0%C sp (size_seqpoly sp).-1.

(* More efficient version that only require one go through the list *)
(* Definition lead_coef_seqpoly : seqpoly -> T := *)
(*   let fix aux x p := *)
(*       if p is a :: p then  *)
(*          if (a == 0)%C then aux x p else aux a p *)
(*       else x in aux 0. *)

(* polyC *)
Global Instance embed_seqpoly : cast_class T seqpoly := fun a => nseq (~~ (a == 0)%C) a.

(* Spliting a polynomial, useful for karatsuba *)
Definition split_seqpoly n (p : seqpoly) := (drop n p, take n p).

(* multiplication, when everything works, repace by karatsuba? *)
Global Instance mul_seqpoly : mul seqpoly := fun p q =>
  let fix aux p := 
      if p is a :: p then (a *: q + shift 1%N (aux p))%C else 0%C
  in aux p.

(* Horner evaluation *)
Fixpoint horner_seq (s : seqpoly) x := 
  if s is a :: s' then (horner_seq s' x * x + a)%C else 0%C.

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

Definition edivp_seqpoly (p q : seqpoly) : nat * seqpoly * seqpoly :=
  if (q == 0)%C then (0%N, 0%C, p) else edivp_rec_seqpoly q 0 0%C p (size_seqpoly p).

Definition divp_seqpoly p q  := (edivp_seqpoly p q).1.2.
Definition modp_seqpoly p q  := (edivp_seqpoly p q).2.
Definition scalp_seqpoly p q := (edivp_seqpoly p q).1.1.

End seqpoly_ops.
End seqpoly.

(***********************************************************)
(* PART II: Proving the properties of the previous objects *)
(***********************************************************)
Section seqpoly_ring.
Variable A : ringType.

Instance zeroA : zero A := 0%R.
Instance oneA  : one A  := 1%R.
Instance addA  : add A  := +%R.
Instance oppA  : opp A  := -%R.
Instance subA  : sub A  := subr.
Instance mulA  : mul A  := *%R.
Instance eqA   : eq A   := eqtype.eq_op.

Lemma seqpoly_of_polyK : pcancel (@polyseq A) (some \o Poly).
Proof. by move=> p /=; rewrite polyseqK. Qed.

Definition Rpoly : {poly A} -> seqpoly A -> Prop := fun_hrel Poly.

Program Instance refinement_poly_seqpoly :
  refinement Rpoly := Refinement seqpoly_of_polyK _.
Next Obligation. by split=> [??[<-]|??<-]. Qed.

Lemma refines_polyE p q : param refines p q -> p = Poly q.
Proof. by case. Qed.

(* zero and one *)
Instance refines_seqpoly0 : param refines 0%R 0%C.
Proof. by rewrite paramE. Qed.

Instance refines_seqpoly1 : param refines 1%R 1%C.
Proof. 
by rewrite paramE /refines /Rpoly /fun_hrel /= cons_poly_def mul0r add0r. 
Qed.

(* drop_zero *)
Lemma Poly_rcons : forall (s : seq A), Poly (rcons s 0) = Poly s.
Proof. by elim=> /= [|a s ->] //; rewrite cons_poly_def mul0r add0r. Qed.

Definition drop0p := @idfun {poly A}.

Lemma refines_drop_zero :
 param (refines ==> refines) drop0p (@drop_zero _ _ _).
Proof.
apply param_abstr => _ sp <-.
elim/last_ind: sp => //= s a.
rewrite /drop_zero rev_rcons /=; simpC => ih.
have [->|_] := (altP eqP); last by rewrite rev_cons revK.
by rewrite Poly_rcons.
Qed.

(* zippolywith *)
Lemma zippolywithE R (f : A -> A -> R) (p q : seqpoly A) :
  zippolywith f p q = mkseq (fun i => f (nth 0 p i) (nth 0 q i))
                            (maxn (size p) (size q)).
Proof.
have sz : size (zippolywith f p q) = (maxn (size p) (size q)).
  move=> z.
  elim: p q => [|a p ihp] [|b q] //=; do ?by rewrite size_map ?maxn0.
  by rewrite ihp maxnSS.
case hz: zippolywith sz => [|z s] /(_ zeroA); first by rewrite hz => <-. 
rewrite -hz => {hz} sz. 
apply: (@eq_from_nth _ z); first by rewrite size_mkseq sz.
move=> i; rewrite sz => hi; rewrite nth_mkseq // => {sz}.
elim: p q i hi => [|a p ihp] [|b q] [|i] //=;
rewrite ?nth_nil (maxn0, max0n, maxnSS) ltnS => hi; rewrite ?(nth_map 0) //.
by rewrite ihp.
Qed.

(* addition *)
Instance refines_seqpoly_add : 
  param (refines ==> refines ==> refines) +%R +%C.
Proof.
apply param_abstr2 => /= x a xa y b yb.
apply/polyP => i; rewrite /add_op /add_seqpoly /= zippolywithE.
rewrite [x]refines_polyE [y]refines_polyE /= coef_Poly.
have [i_small|i_large] := ltnP i (maxn (size a) (size b)).
  by rewrite nth_mkseq // coef_add_poly //= !coef_Poly.
rewrite !nth_default // ?size_mkseq //.
rewrite (leq_trans (leq_trans (size_add _ _) _) i_large) //.
by rewrite geq_max !leq_max !size_Poly orbT.
Qed.

(* negation *)
Instance refines_seqpoly_opp : param (refines ==> refines) -%R -%C.
Proof.
apply param_abstr=> /= x a xa.
apply/polyP => i /=; rewrite /opp_op /opp_seqpoly /=.
rewrite [x]refines_polyE coef_opp_poly !coef_Poly.
have [hlt|hleq] := ltnP i (size a); first by rewrite (nth_map 0%C).
by rewrite !nth_default ?oppr0 ?size_mkseq ?size_map.
Qed.

(* subtraction *)
Instance refines_seqpoly_sub : param (refines ==> refines ==> refines) 
  (fun x y => x - y)%R (fun a b => a - b)%C.
Proof.
apply param_abstr2 => /= x a xa y b yb.
apply/polyP => i; rewrite /sub_op /sub_seqpoly /= zippolywithE.
rewrite [x]refines_polyE [y]refines_polyE /= coef_Poly.
have [i_small|i_large] := ltnP i (maxn (size a) (size b)).
  by rewrite nth_mkseq // coef_add_poly //= coef_opp_poly !coef_Poly. 
rewrite !nth_default // ?size_mkseq //.
rewrite (leq_trans (leq_trans (size_add _ _) _) i_large) //.
by rewrite size_opp geq_max !leq_max !size_Poly orbT.
Qed.

(* splitting *)
Lemma refines_seqpoly_split n (p : {poly A}) (q : seqpoly A) :
   refines p q -> refines (rdivp p 'X^n, rmodp p 'X^n) (split_seqpoly n q).
Proof.
move=> <- {p}; rewrite /refines /Rpoly /fun_hrel /prod_hrel /= paramE.
apply/pair_andP.
elim: q n => //= [|b q ihq] [|n]; do ?by rewrite ?(rdiv0p, rmod0p).
  by rewrite //= cons_poly_def expr0 ?(rdivp1, rmodp1).
rewrite /= !cons_poly_def [Poly q](@rdivp_eq _ 'X^n) ?monicXn //.
have [-> ->] := ihq n; rewrite mulrDl -mulrA -exprSr -addrA.
suff htnq: size (rmodp (Poly q) 'X^n * 'X + b%:P) < size ('X^n.+1 : {poly A}).
  by rewrite rdivp_addl_mul_small ?rmodp_addl_mul_small ?monicXn //.
rewrite size_polyXn size_MXaddC ltnS; case: ifP => // _.
by rewrite (leq_trans (ltn_rmodpN0 _ _)) ?monic_neq0 ?monicXn ?size_polyXn.
Qed.

Lemma refines_seqpoly_split1 n p q :
  refines p q -> refines (rdivp p 'X^n) (split_seqpoly n q).1.
Proof. by move=> /refines_seqpoly_split -/(_ n)=> [] [/= <-]. Qed.

Lemma refines_seqpoly_split2 n p q :
  refines p q -> refines (rmodp p 'X^n) (split_seqpoly n q).2.
Proof. by move=> /refines_seqpoly_split -/(_ n)=> [] [/= ? <-]. Qed.

(* scaling *)
Instance refines_seqpoly_scale : param (Logic.eq ==> refines ==> refines) *:%R *:%C.
Proof.
apply param_abstr2 => /= a b -> {a} p s ps.
apply/polyP => i /=; rewrite [p]refines_polyE coefZ !coef_Poly.
have [hlt|hleq] := ltnP i (size s); first by rewrite (nth_map 0%C).
by rewrite !nth_default ?mulr0 ?size_mkseq ?size_map.
Qed.

(* shifting = * 'X^n *)
Instance refines_seqpoly_shift : param (Logic.eq ==> refines ==> refines) 
  (fun n p => p * 'X^n) (fun n => shift n).
Proof.
apply param_abstr2 => /= m n -> {m} p s ps.
by apply/polyP => i /=; rewrite [p]refines_polyE coefMXn !coef_Poly nth_ncons.
Qed.


Instance refines_seqpoly_cons : param (Logic.eq ==> refines ==> refines) 
  (fun a p => p * 'X + a%:P) (fun a s => a :: s).
Proof.
apply param_abstr2 => /= b a -> {b} p s ps.
by apply/polyP => i /=; rewrite [p]refines_polyE cons_poly_def.
Qed.

(* maybe this should be "all (fun x => x == 0) s" ? *)
Lemma refines_poly0 (s : seqpoly A) : param refines 0 s ->
  forall x, x \in s -> x = 0.
Proof. 
move=> hs x /(nthP 0) [i hi <-].
by rewrite -coef_Poly -(refines_polyE hs) coef0. 
Qed.

Lemma refines_poly_MXaddC a p (s : seqpoly A) :
  param refines (p * 'X + a%:P) s -> param refines p (behead s) /\ a = (head 0 s).
Proof.
wlog -> : s / s = (head 0 s) :: (behead s) => [hwlog|].
  case: s => [rp|x s]; last by apply: hwlog.
  have /= := hwlog [::0] erefl; rewrite [_ + _]refines_polyE /= => H; apply H.
  by apply/polyP=> i /=; rewrite cons_poly_def mul0r addr0.
(* What to do here? *)
(* rewrite /refines /Rpoly /fun_hrel /= cons_poly_def => [[hp]]. *)
(* have := congr1 (fun p => some (rdivp p 'X)) hp. *)
(* have := congr1 (fun p => (rmodp p 'X)) hp. *)
(* rewrite ?(rdivp_addl_mul_small, rmodp_addl_mul_small); *)
(*   do ?by rewrite ?monicX ?size_polyC ?size_polyX ?ltnS ?leq_b1. *)
(* by move=> /polyC_inj. *)
admit.
Qed.

Lemma refines_poly0_cons a s : refines 0 (a :: s) -> (refines 0 s /\ a = 0).
Proof.
have {1}-> : 0 = 0 * 'X + 0%:P :> {poly A} by rewrite mul0r addr0.
by move/refines_poly_MXaddC => [? ->].
Qed.

Lemma refines_poly_cons p x s : refines p (x :: s) ->
  {pa | [/\ p = pa.1 * 'X + pa.2%:P, pa.2 = x & refines pa.1 s]}.
Proof.
elim/poly_ind: p => [|p a ihp] in s *.
  by move=> /refines_poly0_cons [rs ->]; exists 0; rewrite mul0r add0r.
by move=> /refines_poly_MXaddC /= [rps ->]; exists (p, x).
Qed.

(* size *)
Instance refines_seqpoly_size : param (refines ==> Logic.eq) 
  (fun (p : {poly A}) => size p) (fun s => size_seqpoly s).
Proof.
apply param_abstr => p s ps.
symmetry; elim: s => [|x sp ihs] //= in p ps *.
  by rewrite [p]refines_polyE size_poly0.
move: ps => /refines_poly_cons [[p' a /= [-> -> rp']]].
rewrite (ihs p' rp') size_poly_eq0 size_MXaddC; simpC.
by have [->|] //= := (altP eqP); case: ifP => //=; rewrite size_poly0.
Qed.

(* lead_coef *)
Instance refines_seqpoly_lead_coef : 
  param (refines ==> Logic.eq) lead_coef (fun p => lead_coef_seqpoly p).
Proof.
apply param_abstr => p s ps; rewrite /lead_coef_seqpoly /lead_coef.
rewrite (refines_seqpoly_size ps). (* Why do I have to give ps? *)
by rewrite [p]refines_polyE coef_Poly.
Qed.

(* polyC *)
Instance refines_seqpoly_polyC : param (Logic.eq ==> refines) (fun a => a%:P) (fun a => cast a)%C.
Proof.
apply param_abstr => b a -> {b}.
rewrite /cast /embed_seqpoly; simpC.
have [->|_] //= := (altP eqP). 
by apply/polyP=> i /=; rewrite cons_poly_def mul0r add0r.
Qed.

(* multiplication *)
Instance refines_poly_mul : param (refines ==> refines ==> refines) *%R *%C.
Proof.
apply param_abstr2 => /= p sp rp q sq rq.
elim: sp => [|a sp ihp] in p rp *; first by rewrite [p]refines_polyE mul0r.
move: rp => /refines_poly_cons [[sp' a' /= [-> -> rp']]].
admit.
(* This does not work anymore... *)
(* move: rp => /refines_poly_cons [[sp' a' /= [-> -> rp']]]; apply/refinesP. *)
(* by rewrite mulrDl addrC mul_polyC addr0 -mulrA !(commr_polyX, mulrA). *)
Qed.

(* equality *)
Instance refines_poly_eq : param (refines ==> refines ==> Logic.eq) 
  (fun p q => p == q) (fun sp sq => sp == sq)%C.
Proof.
apply param_abstr2 => p sp hsp q sq hsq.
rewrite /eq_op /eq_seqpoly zippolywithE [p]refines_polyE [q]refines_polyE.
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
Instance refines_seqpoly_horner : param (refines ==> Logic.eq ==> Logic.eq) 
  (fun p x => p.[x]) (fun sp x => horner_seq sp x).
Proof.
apply param_abstr2 => p sp hsp x' x -> {x'}.
elim: sp => [|a sp ih] //= in p hsp *; first by rewrite [p]refines_polyE /= horner0.
move: hsp => /refines_poly_cons [[p' b /= [-> -> rp']]].
by rewrite -cons_poly_def horner_cons (ih _ rp'); simpC. (* Why do I have to give rp' to ih? *)
Qed.

(* pseudo-division *)
(* Lemma refines_edivp_rec_seqpoly : forall n k (q qq r : {poly A}) (sq sqq sr : seqpoly A) *)
(*   (rq : param refines q sq) (rqq : param refines qq sqq)  *)
(*   (rr : param refines r sr), *)
(*   let: (l,a,b)    := redivp_rec q k qq r n in  *)
(*   let: (l',sa,sb) := edivp_rec_seqpoly sq k sqq sr n in  *)
(*   l = l' /\ refines (a, b) (sa, sb). *)
(* Proof. *)
(* elim=> [|n ih] k q qq r sq sqq sr rq rqq rr /=;  *)
(* rewrite -!refines_seqpoly_size -!refines_seqpoly_lead_coef -!mul_polyC; *)
(* case: ifP => _; do ?split; do ?eapply ih=> //. *)
(* by apply/refinesP.  *)
(* Admitted. *)

(* Lemma refines_edivp_seqpoly p q (sp sq : seqpoly A) *)
(*   (rp : refines p sp) (rq : refines q sq) : *)
(*   let: (l,a,b)    := redivp p q in  *)
(*   let: (l',sa,sb) := edivp_seqpoly sp sq in  *)
(*   l = l' /\ refines (a, b) (sa, sb). *)
(* Proof. *)
(* rewrite /redivp unlock /redivp_expanded_def /edivp_seqpoly. *)
(* rewrite -refines_poly_eq -refines_seqpoly_size. *)
(* (* case: ifP => _; first by split=> //; apply/refinesP. *) *)
(* (* exact: refines_edivp_rec_seqpoly. *) *)
(* (* Qed. *) *)
(* Admitted. *)

(* Global Instance refines_seqpoly_divp (p q : {poly A}) (sp sq : seqpoly A) *)
(*   (rp : refines p sp) (rq : refines q sq) : refines (rdivp p q) (divp_seqpoly sp sq). *)
(* Proof. *)
(* rewrite /rdivp /divp_seqpoly; move: (refines_edivp_seqpoly rp rq). *)
(* by case: redivp => [[a b c]]; case: edivp_seqpoly => [[sa sb sc]] [/= _ [->]]. *)
(* Qed. *)

(* Global Instance refines_seqpoly_modp (p q : {poly A}) (sp sq : seqpoly A) *)
(*   (rp : refines p sp) (rq : refines q sq) : refines (rmodp p q) (modp_seqpoly sp sq). *)
(* Proof. *)
(* rewrite /rmodp /modp_seqpoly; move: (refines_edivp_seqpoly rp rq). *)
(* by case: redivp => [[a b c]]; case: edivp_seqpoly => [[sa sb sc]] [/= _ [_ ->]]. *)
(* Qed. *)

(* Lemma refines_seqpoly_scalp (p q : {poly A}) (sp sq : seqpoly A) *)
(*   (rp : refines p sp) (rq : refines q sq) : rscalp p q = scalp_seqpoly sp sq. *)
(* Proof. *)
(* rewrite /rscalp /scalp_seqpoly; move: (refines_edivp_seqpoly rp rq). *)
(* by case: redivp => [[a b c]]; case: edivp_seqpoly => [[sa sb sc]] []. *)
(* Qed. *)

End seqpoly_ring.

(*************************************************************************)
(* PART III: Parametric part                                             *)
(*************************************************************************)
Section Qparametric.

(* TODO: Finish! *)

End Qparametric.


(* This does not work as seqpoly is not using parametricity yet! *)
(* (* Some tests *) *)
(* Require Import ZArith ssrint binint. *)

(* Eval compute in (0 + 0)%C : seqpoly Z. *)
(* Eval compute in (1 + 1)%C : seqpoly Z. *)
(* Eval compute in 1%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1)%C : seqpoly (seqpoly Z). *)
(* Eval compute in (1 + 1 + 1 + 1 + 1)%C : *)
(*   seqpoly (seqpoly (seqpoly (seqpoly (seqpoly Z)))). *)