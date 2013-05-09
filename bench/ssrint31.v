Require Import Int31.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix refinements.

Import Refinements.Op.

Open Scope int31_scope.

Global Instance zero_int : zero int := 0.

Global Instance one_int : one int := 1.

Global Instance opp_int : opp int := Int31Op.opp.

Global Instance add_int : add int := Int31Native.add.

Global Instance sub_int : sub int := Int31Native.sub.

Global Instance mul_int : mul int := Int31Native.mul.

Global Instance eq_int : eq int := Int31Native.eqb.
