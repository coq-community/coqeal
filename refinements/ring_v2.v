From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg ssrint.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.
From mathcomp Require Import zmodp.

From SsrMultinomials Require Import mpoly.

From CoqEAL Require Import hrel param refinements binint poly_op hpoly karatsuba multipoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

Local Open Scope ring_scope.

Ltac mem_tuple s t :=
  let rec aux s :=
      match s with
      | [::] => constr:(false)
      | (?hd :: ?tl) => match hd with
                        | t => constr:(true)
                        | _ => aux tl
                        end
      end in
  let s' := (eval simpl in (tval s)) in
  aux s'.

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
      | _ => let b := mem_tuple fv t in
             match b with
             | true => fv
             | false => constr:([tuple of t :: fv])
             end
      end in
  let s := aux t ([tuple] : 0.-tuple A) in
  let n := (eval compute in (size s)) in
  constr:((s, n)).

Inductive PExpr N :=
  | PEc : int -> PExpr N
  | PEX : 'I_N -> PExpr N
  | PEadd : PExpr N -> PExpr N -> PExpr N
  | PEmul : PExpr N -> PExpr N -> PExpr N
  | PEopp : PExpr N -> PExpr N
  | PEpow : PExpr N -> nat -> PExpr N.

Definition PExpr_to_poly N : PExpr N -> {mpoly int[N]} :=
  fix aux p := match p with
  | PEc n => n%:MP
  | PEX n => 'X_n
  | PEadd p q => aux p + aux q
  | PEmul p q => aux p * aux q
  | PEopp p => - aux p
  | PEpow p n => aux p ^+ n
end.

Definition PExpr_to_Expr (R : ringType) N (env : N.-tuple R) : PExpr N -> R :=
  fix aux p := match p with
  | PEc n => n%:~R
  | PEX n => env`_n
  | PEadd p q => aux p + aux q
  | PEmul p q => aux p * aux q
  | PEopp p => - aux p
  | PEpow p n => aux p ^+ n
end.

Lemma mevalXX n (R : comRingType) (v : 'I_n -> R) m :
  {morph meval v : p / p ^+ m >-> p ^+ m}.
Proof.
move=> p; elim: m => [|m ihm]; first by rewrite !expr0 mevalC.
by rewrite !exprS mevalM ihm.
Qed.

Lemma polyficationP (R : comRingType) N (env : N.-tuple R) p :
  PExpr_to_Expr env p = (map_mpoly intr (PExpr_to_poly p)).@[tnth env].
Proof.
elim: p => [n|n|p IHp q IHq|p IHp q IHq|p IHp|p IHp n] /=.
- by rewrite map_mpolyC mevalC.
- by rewrite map_mpolyX mevalXU (tnth_nth 0).
- by rewrite rmorphD mevalD IHp IHq.
- by rewrite rmorphM mevalM IHp IHq.
- by rewrite rmorphN mevalN IHp.
- by rewrite rmorphX mevalXX IHp.
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
  let s' := eval simpl in (tval fv) in
  aux s' O.

Ltac toPExpr t fv N :=
  let rec aux t :=
      match t with
      | 0 => uconstr:(PEc N.+1 0)
      | 1 => uconstr:(PEc N.+1 1)
      | (?t1 + ?t2) => let e1 := aux t1 in
                       let e2 := aux t2 in
                       uconstr:(PEadd e1 e2)
      | (?t1 * ?t2) => let e1 := aux t1 in
                       let e2 := aux t2 in
                       uconstr:(PEmul e1 e2)
      | (- ?t) => let e := aux t in
                  uconstr:(PEopp e)
      | ?n%:~R => uconstr:(PEc N.+1 n)
      | _ => let n := getIndex t fv in uconstr:(PEX (inZp n))
      end in
  let e := aux t in constr:(e : PExpr N.+1).

Tactic Notation (at level 0) "translate" constr(t) :=
  let A := type of t in
  let c := freeVars t A in
  let fv := (eval simpl in [tuple of 0 :: c.1]) in
  let n := (eval simpl in (c.2)) in
  let p := toPExpr t fv n in
  have /= := @polyficationP _ n.+1 fv p.

Tactic Notation "polyfication" :=
  match goal with
  | |- (eq ?lhs ?rhs) =>
    let A := type of lhs in
    let c := freeVars (lhs + rhs) A in
    let fv := (eval simpl in [tuple of 0 :: c.1]) in
    let n := (eval simpl in (c.2)) in
    let pl := toPExpr lhs fv n in
    let pr := toPExpr rhs fv n in
    let rwl := fresh "rwl" in
    let rwr := fresh "rwr" in
    have /= rwl := @polyficationP _ n.+1 fv pl; rewrite [LHS]rwl {rwl};
    have /= rwr := @polyficationP _ n.+1 fv pr; rewrite [RHS]rwr {rwr}
  | _ => fail "goal not an equation"
  end.

Tactic Notation "polyfication'" :=
  match goal with
  | |- (eq ?lhs ?rhs) =>
    let A := type of lhs in
    let c := freeVars (lhs - rhs) A in
    let fv := (eval simpl in [tuple of 0 :: c.1]) in
    let n := (eval simpl in (c.2)) in
    let p := toPExpr (lhs - rhs) fv n in
    apply: subr0_eq;
    have /= -> := @polyficationP _ n.+1 fv p;
    let rw := fresh "rw" in
    have /= rw := @polyficationP _ n.+1 fv (PEc n.+1 0); rewrite [RHS]rw {rw};
    congr (map_mpoly _ _).@[_]
  | _ => fail "goal not an equation"
  end.

Tactic Notation "depolyfication" :=
  do ?[rewrite ?(rmorph0, rmorphN, rmorphD, rmorphB,
                rmorph1, rmorphM, rmorphX, map_mpolyC,
                map_mpolyX, map_mpolyZ) /=];
  do ?[rewrite ?(meval0, mevalN, mevalD, mevalB, mevalC, meval1, mevalXU,
                 mevalZ, mevalM, mevalXX, mevalX) /=];
  rewrite ?big_ord_recl /= ?big_ord0 ?mulr1 ?(tnth_nth 0) /= ?expr0n /= ?mul1r.

Tactic Notation "coqeal_vm_compute_eq2" :=
  do 1?coqeal [(X in (map_mpoly _ X).@[_] = _)%pattern] vm_compute;
  do 1?coqeal [(X in _ = (map_mpoly _ X).@[_])%pattern] vm_compute.

(* Tactic Notation "coqeal_ring" := *)
(*   by polyfication; coqeal_vm_compute_eq2; depolyfication. *)

Tactic Notation "coqeal_ring" :=
  by polyfication'; coqeal.

Goal true.

  (* Typeclasses eauto := debug. *)

  have (a : int) : a - a * 1 = 0.
  polyfication.
  coqeal_vm_compute_eq2.
  depolyfication.
  (* polyfication'. *)
  (* by coqeal. *)
  Time by coqeal_ring.
  move=> _.

  have (a b c : {poly int}) : a * (b + c) = a * b + a * c.
  polyfication.
  coqeal_vm_compute_eq2.
  depolyfication.
  (* polyfication. *)
  (* Fail coqeal [(X in map_mpoly _ X)%pattern] vm_compute. *)
  (* congr (map_mpoly _ _).@[_]. *)
  (* apply/eqP. *)
  (* by coqeal. *)
  Time by coqeal_ring.
  move=> _.

  have (a b c d e f : int) : a * (b + c) + d * e - f = a * b + a * c + d * e - f.
  Time polyfication'.
  Time by coqeal.
  (* Time by coqeal_ring. *)
  move=> _.

  have (a b c : {poly int}) : (b + c) * a = b * a + c * a.
  polyfication.
  coqeal_vm_compute_eq2.
  Time polyfication'.
  Time by coqeal.
  (* Time by coqeal_ring. *)
  move=> _.

  have (a : {poly int}) : a * 0 = 0.
  polyfication.
  coqeal_vm_compute_eq2.
  rewrite ?mevalX /=.
  Time polyfication'.
  Time by coqeal.
  (* Time by coqeal_ring. *)
  move=> _.

  have (a : Zp_ringType 7) : 0 = a * 0.
  polyfication.
  coqeal_vm_compute_eq2.
  Time polyfication'.
  Time by coqeal.
  (* Time by coqeal_ring. *)
  move=> _.

  have (a : {poly {poly {poly int}}}) : a * 0 = 0.
  polyfication.
  coqeal_vm_compute_eq2.
  Time polyfication'.
  Time by coqeal.
  (* Time by coqeal_ring. *)
  move=> _.

  have (R : comRingType) (a b c : R) : a + b - (1 * b + c * 0) = a.
  polyfication.
  coqeal [(X in (map_mpoly _ X).@[_])%pattern] vm_compute.
  coqeal_vm_compute_eq2.
  depolyfication.
  admit.
  (* Time polyfication'. *)
  (* Time by coqeal. *)
  (* Time by coqeal_ring. *)
  move=> _.
by[].
Admitted.