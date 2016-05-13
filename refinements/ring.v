From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq ssralg ssrint.
From mathcomp Require Import path choice fintype tuple finset ssralg bigop poly polydiv.

From CoqEAL Require Import hrel param refinements binint poly_op hpoly karatsuba.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Import Refinements.Op Poly.Op.

Local Open Scope ring_scope.

Ltac simplify y p := let l := fresh "to_rewrite" in
                   pose (l := p); generalize (eq_refl l);
                   rewrite -[X in (_ == X)]/(spec_id _) [spec_id _]refines_eq /=
                                           /l;
                   move/eqP=> y;
                   clear l.

Tactic Notation (at level 0) "pose_simpl" ident(x) ":=" constr(p) :=
  simplify x p.

Ltac polyType n :=
  let rec aux n :=
      match n with
      | O => uconstr:{poly int}
      | (S ?n) => let A := aux n in
                  uconstr:{poly A}
      end in
  let A := aux n in constr:A.

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

Ltac makeX n :=
  let rec aux n :=
      match n with
      | O => uconstr:('X)
      | (S ?n) => let x := aux n in
                  uconstr:(x%:P)
      end in
  aux n.

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

Ltac const n A :=
  let rec aux A :=
      match A with
      | {poly ?A} => let c := aux A in
                     uconstr:(c%:P)
      | _ => uconstr:(n%:Z)
      end in
  aux A.

Ltac toPoly t fv T :=
  let rec aux t :=
      match t with
      | 0 => uconstr:0
      | 1 => uconstr:1
      | (?t1 + ?t2) => let e1 := aux t1 in
                       let e2 := aux t2 in
                       uconstr:(e1 + e2)
      | (?t1 - ?t2) => let e1 := aux t1 in
                       let e2 := aux t2 in
                       uconstr:(e1 - e2)
      | (?t1 * ?t2) => let e1 := aux t1 in
                       let e2 := aux t2 in
                       uconstr:(e1 * e2)
      | (- ?t) => let e := aux t in
                  uconstr:(- e)
      | ?n%:~R => const n T
      | _ => let n := getIndex t fv in
             makeX n
      end in
  let e := aux t in constr:(e : T).

Ltac lift n t :=
  let rec aux n :=
      match n with
      | O => t
      | (S ?n) => let e := aux n in
                  uconstr:(e%:P)
      | _ => fail "lift"
      end in
  let e := aux n in constr:e.

Ltac cast p T :=
  let rec aux T :=
      match T with
      | {poly ?T} => let f := aux T in
                     uconstr:(map_poly f)
      | _ => uconstr:(intr)
      end in
  let f := aux T in
  uconstr:(f p).

Ltac haveHorner p s n t T :=
  let rec aux s n acc :=
      match s with
      | [::] => uconstr:(acc.[0])
      | (?h :: ?t) => let e := lift n h in
                      let p' := uconstr:(acc.[e]) in
                      let n' := (eval compute in n.-1) in
                      aux t n' p'
      end in
  let p' := cast p T in
  let e := aux s n p' in
  have : (t = e)
    by rewrite ![map_poly_rmorphism _ _](rmorph0, rmorphN, rmorphD, rmorphB,
                                         rmorph1, rmorphM, map_polyC,
                                         map_polyX)
               ?[GRing.Additive.apply _ _](map_polyC, map_polyX) !hornerE.

Tactic Notation (at level 0) "translate" constr(t) :=
  let A := type of t in
  let c := freeVars t A in
  let fv := (eval simpl in (c.1)) in
  let n := (eval simpl in (c.2)) in
  let T := polyType n in
  let p := toPoly t fv T in
  let pol := fresh "P" in
  pose pol := p;
  haveHorner pol fv n t T;
  move: @pol.

Tactic Notation "translateEq" :=
  match goal with
  | |- (eq ?lhs ?rhs) =>
    let A := type of lhs in
    let c := freeVars (lhs + rhs) A in
    let fv := (eval simpl in (c.1)) in
    let n := (eval simpl in (c.2)) in
    let T := polyType n in
    let pl := toPoly lhs fv T in
    let pol := fresh "Pl" in
    pose pol := pl;
    haveHorner pol fv n lhs T;
    let heq := fresh "to_rewrite" in
    move=> heq;
    rewrite [LHS]heq;
    clear heq;
    move: @pol;
    let pr := toPoly rhs fv T in
    let pol := fresh "Pr" in
    pose pol := pr;
    haveHorner pol fv n rhs T;
    let heq := fresh "to_rewrite" in
    move=> heq;
    rewrite [X in let _ := _ in _ = X]heq;
    clear heq;
    move: @pol
  | _ => fail "bad goal"
  end.

Tactic Notation "simplPoly" :=
  rewrite -[X in let _ := _ in let _ := X in _]/(spec_id _)
          -[X in let _ := X in _]/(spec_id _)
          ![spec_id _]refines_eq /=.

Tactic Notation "evalHorner" :=
  do ?[rewrite ![map_poly_rmorphism _ _](rmorph0, rmorphN, rmorphD, rmorphB,
                                        rmorph1, rmorphM, map_polyC,
                                        map_polyX, map_polyZ)
      |rewrite ![GRing.Additive.apply _ _](rmorph0, rmorphN, rmorphD, rmorphB,
                                         rmorph1, rmorphM, map_polyC,
                                         map_polyX, map_polyZ)
      |rewrite ![GRing.Rmorphism.apply _ _](rmorph0, rmorphN, rmorphD, rmorphB,
                                         rmorph1, rmorphM, map_polyC,
                                         map_polyX, map_polyZ)];
  rewrite !hornerE.

Tactic Notation "CoqEALRing" :=
  by translateEq; simplPoly; evalHorner.

Goal true.
  
  pose_simpl h0 := (- (1 + 'X%:P * 'X) : {poly {poly int}}).
  pose_simpl h1 := (2%:Z%:P + 'X - 1 * 2%:Z%:P).
  pose_simpl h2 :=
    ((1 + 2%:Z *: 'X) * (1 + 2%:Z%:P * 'X^(sizep (1 : {poly int})))).
  pose_simpl h3 :=
    (1 + 2%:Z *: 'X + 3%:Z *: 'X^2 - (3%:Z *: 'X^2 + 1 + 2%:Z *: 'X)).
  pose_simpl h4 := ('X + 'X^2 * 'X%:P : {poly {poly int}}).

  have (a b c : int) : a * (b + c) = a * b + a * c.
  Time CoqEALRing.
  move=> _.

  have (a b c : {poly int}) : (b + c) * a = b * a + c * a.
  Time CoqEALRing.
  move=> _.

  have (a : {poly int}) : a * 0 = 0.
  Time CoqEALRing.
  move=> _.

  have (a : zmodp.Zp_ringType 7) : 0 = a * 0.
  Time CoqEALRing.
  move=> _.

  have (a : {poly {poly {poly int}}}) : a * 0 = 0.
  Time CoqEALRing.
  move=> _.

  have (R : comRingType) (a b c : R) : a + b - (1 * b + c * 0) = a.
  Time translateEq. (* 28.4 *)
  Time simplPoly. (* 14.6 *)
  Time evalHorner. (* 0.6 *)
  by [].
  (* Time CoqEALRing. *)
  move=> _.
