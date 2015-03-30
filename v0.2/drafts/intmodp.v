Require Import Int31.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice.
Require Import fintype bigop finset prime fingroup ssralg zmodp finalg.

Require Import refinements.

Section operations.

Import Refinements.Op.

Local Open Scope int31_scope.

Let p := 7919.

Global Instance zero_int : zero int := 0.

Global Instance one_int : one int := 1.

Global Instance opp_int : opp int :=
  fun x => p - x.

Global Instance add_int : add int :=
  fun x y => (x + y) \% p.

Global Instance sub_int : sub int :=
  fun x y => if y <= x then x - y
  else p + x - y.

Global Instance mul_int : mul int :=
  fun x y => (x * y) \% p.

(** Gcd **)
Fixpoint egcd_rec (guard:nat) (i j:int) {struct guard} :=
   match guard with
   | O => (1,1) (* TODO: check *)
   | S p => if (j == 0)%int31 then (1,0) else
            let (q, r) := diveucl i j in
            let (s, t) := egcd_rec p j r in
            (t, sub_int s (mul_int q t))
   end.

Definition egcd := egcd_rec (2*Int31Native.size).

Global Instance inv_int : inv int :=
  fun x => snd (egcd p x).

Global Instance eq_int : eq int := Int31Native.eqb.

End operations.