From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg ssrint.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.
From mathcomp Require Import zmodp.

From CoqEAL Require Import hrel param refinements binint poly_op hpoly karatsuba.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

Local Open Scope ring_scope.

Ltac in_seq s t :=
  let rec aux s :=
      match s with
      | [::] => constr:false
      | (?hd :: ?tl) => match hd with
                        | t => constr:true
                        | _ => aux tl
                        end
      end in
  aux s.

Ltac freeVars t A :=
  let rec aux t fv :=
      match t with
      | 0 => fv
      | 1 => fv
      | (?t1 + ?t2) => aux t2 ltac:(aux t1 fv)
      | (?t1 - ?t2) => aux t2 ltac:(aux t1 fv)
      | (?t1 * ?t2) => aux t2 ltac:(aux t1 fv)
      | (- ?t) => aux t fv
      | ?n%:~R => fv
      | _ => let b := in_seq fv t in
             match b with
             | true => fv
             | false => constr:(t :: fv)
             end
      end in
  let s := aux t ([::] : seq A) in
  let n := (eval compute in (size s)) in
  constr:(s, n).

Inductive PExpr :=
  | PEc : int -> PExpr
  | PEX : nat -> PExpr
  | PEadd : PExpr -> PExpr -> PExpr
  | PEmul : PExpr -> PExpr -> PExpr
  | PEopp : PExpr -> PExpr
  | PEpow : PExpr -> nat -> PExpr.

Definition Npoly (R : comRingType) : nat -> comRingType := fix aux n :=
  if n is n.+1 then poly_comRingType (aux n) else R.

Fixpoint NpolyC (R : comRingType) N : R -> Npoly R N :=
  if N isn't N'.+1 return R -> Npoly R N
  then fun x => x
  else fun x => (NpolyC N' x)%:P.

Fixpoint NpolyX (R : comRingType) N : nat -> Npoly R N :=
  if N isn't N'.+1 return nat -> Npoly R N
  then fun=> 0
  else fun n => if n is n.+1 then (NpolyX R N' n)%:P
                else 'X.

Fixpoint Nmap_poly (R R' : comRingType) (f : R -> R') N :
  Npoly R N -> Npoly R' N :=
  if N isn't N'.+1 return Npoly R N -> Npoly R' N
  then f else map_poly (@Nmap_poly _ _ f N').

Section Nmap_poly_morphism.

  Variable R R' : comRingType.
  Variable g : {additive R -> R'}.
  Variable f : {rmorphism R -> R'}.
  Variable N : nat.

  Fact Nmap_poly_is_additive : additive (Nmap_poly g (N:=N)).
  Proof.
    elim: N=> [|N' IHN] /=.
      exact: raddfB.
    exact: map_poly_is_additive (Additive IHN).
  Qed.
  Canonical Nmap_poly_additive := Additive Nmap_poly_is_additive.

  Fact Nmap_poly_is_rmorphism : rmorphism (Nmap_poly f (N:=N)).
  Proof.
    elim: N=> [|N' IHN] /=.
      exact: rmorphismP.
    exact: map_poly_is_rmorphism (RMorphism IHN).
  Qed.
  Canonical Nmap_poly_rmorphism := RMorphism Nmap_poly_is_rmorphism.

End Nmap_poly_morphism.

Fact horner_key : unit. Proof. exact: tt. Qed.

Fixpoint NhornerR (R : comRingType) N : seq R -> Npoly R N -> R :=
      if N isn't N'.+1 return seq R -> Npoly R N -> R
      then fun _ p => p
      else fun env p => if env is a :: env then NhornerR env p.[NpolyC N' a]
                        else NhornerR [::] p.[0].

Lemma NhornerRS (R : comRingType) N (a : R) (env : seq R) (p : Npoly R N.+1) :
  NhornerR (a :: env) p = NhornerR env p.[NpolyC N a].
Proof. by elim: N p. Qed.

Definition Nhorner (R : comRingType) N (env : seq R)
           (p : Npoly [comRingType of int] N) : R
  := locked_with horner_key (@NhornerR _ _) env (Nmap_poly intr p).

Lemma NhornerE (R : comRingType) N (env : seq R)
          (p : Npoly [comRingType of int] N) :
  Nhorner env p = (@NhornerR _ _) env (Nmap_poly intr p).
Proof. by rewrite /Nhorner; case: horner_key. Qed.

Definition PExpr_to_poly N : PExpr -> Npoly [comRingType of int] N :=
  fix aux p := match p with
  | PEc n => n%:~R
  | PEX n => NpolyX _ N n
  | PEadd p q => aux p + aux q
  | PEmul p q => aux p * aux q
  | PEopp p => - aux p
  | PEpow p n => aux p ^+ n
end.

Definition PExpr_to_Expr (R : comRingType) (env : seq R) : PExpr -> R :=
  fix aux p := match p with
  | PEc n => n%:~R
  | PEX n => env`_n
  | PEadd p q => aux p + aux q
  | PEmul p q => aux p * aux q
  | PEopp p => - aux p
  | PEpow p n => aux p ^+ n
end.

Lemma NhornerRC (R : comRingType) N (env : seq R) (a : R) :
  NhornerR env (NpolyC N a) = a.
Proof. by elim: N env=> [|N IHN] [|b env] //=; rewrite hornerC. Qed.

Lemma Nhorner_is_rmorphism (R : comRingType) (N : nat) (env : seq R) :
  rmorphism (@NhornerR R N env).
Proof.
do !split.
- by elim: N env=> [|N IHN] [|a env] p q //=; rewrite hornerD hornerN IHN.
- by elim: N env=> [|N IHN] [|a env] p q //=; rewrite hornerM IHN.
by elim: N env=> [|N IHN] [|b env] //=; rewrite hornerC.
Qed.

Canonical Nhorner_rmorphism (R : comRingType) (N : nat) (env : seq R) :=
  RMorphism (Nhorner_is_rmorphism N env).

Lemma polyficationP (R : comRingType) (env : seq R) N p : size env == N ->
  PExpr_to_Expr env p = Nhorner env (PExpr_to_poly N p).
Proof.
elim: p=> [n|n|p IHp q IHq|p IHp q IHq|p IHp|p IHp n] /=.
- by rewrite NhornerE !rmorph_int.
- rewrite NhornerE; elim: N env n=> [|N IHN] [|a env] [|n] //= senv.
    by rewrite map_polyX hornerX [RHS]NhornerRC.
  by rewrite map_polyC hornerC !IHN.
- by move=> senv; rewrite (IHp senv) (IHq senv) !NhornerE !rmorphD.
- by move=> senv; rewrite (IHp senv) (IHq senv) !NhornerE !rmorphM.
- by move=> senv; rewrite (IHp senv) !NhornerE !rmorphN.
- by move=> senv; rewrite (IHp senv) !NhornerE !rmorphX.
Qed.

Ltac getIndex t fv :=
  let rec aux s n :=
      match s with
      | (?hd :: ?tl) => match hd with
                        | t => eval compute in n
                        | _ => aux tl uconstr:(n.+1)
                        end
      | _ => fail "Not found"
      end in
  aux fv O.

Ltac toPExpr t fv N :=
  let rec aux t :=
      match t with
      | 0 => uconstr:(PEc 0)
      | 1 => uconstr:(PEc 1)
      | (?t1 + ?t2) => let e1 := aux t1 in
                       let e2 := aux t2 in
                       uconstr:(PEadd e1 e2)
      | (?t1 * ?t2) => let e1 := aux t1 in
                       let e2 := aux t2 in
                       uconstr:(PEmul e1 e2)
      | (- ?t) => let e := aux t in
                  uconstr:(PEopp e)
      | ?n%:~R => uconstr:(PEc n)
      | _ => let n := getIndex t fv in uconstr:(PEX n)
      end in
  let e := aux t in constr:(e : PExpr).

Tactic Notation (at level 0) "translate" constr(t) :=
  let A := type of t in
  let c := freeVars t A in
  let fv := (eval simpl in (c.1)) in
  let n := (eval simpl in (c.2)) in
  let p := toPExpr t fv n in
  have /= := @polyficationP _ fv n p isT.

Tactic Notation "polyfication" :=
  match goal with
  | |- (eq ?lhs ?rhs) =>
    let A := type of lhs in
    let c := freeVars (lhs + rhs) A in
    let fv := (eval simpl in (c.1)) in
    let n := (eval simpl in (c.2)) in
    let pl := toPExpr lhs fv n in
    let pr := toPExpr rhs fv n in
    let rwl := fresh "rwl" in
    let rwr := fresh "rwr" in
    have /= rwl := @polyficationP _ fv n pl isT; rewrite [LHS]rwl {rwl};
    have /= rwr := @polyficationP _ fv n pr isT; rewrite [RHS]rwr {rwr}
  | _ => fail "goal not an equation"
  end.

Tactic Notation "depolyfication" :=
  rewrite NhornerE /NhornerR /=;
  do ?[rewrite ?(rmorph0, rmorphN, rmorphD, rmorphB,
                rmorph1, rmorphM, rmorphX, map_polyC,
                map_polyX, map_polyZ) /=]; rewrite ?hornerE.

Tactic Notation "coqeal_simpl" :=
  rewrite -1?[X in Nhorner _ X = _]/(spec_id _)
          -1?[X in _ = Nhorner _ X]/(spec_id _)
          ![spec_id _]refines_eq /=.

Tactic Notation "CoqEALRing" :=
  by polyfication; coqeal_simpl; depolyfication.

Goal true.

  assert (h1 := coqeal_vm_compute (- (1 + 'X%:P * 'X) : {poly {poly int}})).
  assert (h2 := coqeal_vm_compute
    ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X^(sizep (1 : {poly int}))))).
  assert (h3 := coqeal_vm_compute
    (1 + 2%:Z *: 'X + 3%:Z *: 'X^2 - (3%:Z *: 'X^2 + 1 + 2%:Z%:P * 'X))).
  assert (h4 := coqeal_vm_compute ('X + 'X^2 * 'X%:P : {poly {poly int}})).

  have (a b c : int) : a * (b + c) = a * b + a * c.
  Time by CoqEALRing.
  move=> _.

  have (a b c : {poly int}) : (b + c) * a = b * a + c * a.
  Time by CoqEALRing.
  move=> _.

  have (a : {poly int}) : a * 0 = 0.
  Time by CoqEALRing.
  move=> _.

  have (a : Zp_ringType 7) : 0 = a * 0.
  Time by CoqEALRing.
  move=> _.

  have (a : {poly {poly {poly int}}}) : a * 0 = 0.
  Time by CoqEALRing.
  move=> _.

  have (R : comRingType) (a b c : R) : a + b - (1 * b + c * 0) = a.
  Time by CoqEALRing.
  move=> _.
by[].
Qed.