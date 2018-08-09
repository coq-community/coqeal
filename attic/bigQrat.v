(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import QArith BigQ.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice.
Require Import fintype bigop finset prime fingroup ssralg zmodp finalg refinements.

Section operations.

Import Refinements.Op.

Local Open Scope bigQ_scope.

Global Instance zero_bigQ : zero bigQ := 0.

Global Instance one_bigQ : one bigQ := 1.

Global Instance opp_bigQ : opp bigQ := BigQ.opp.

Global Instance add_bigQ : add bigQ := BigQ.add_norm.

Global Instance sub_bigQ : sub bigQ := BigQ.sub_norm.

Global Instance mul_bigQ : mul bigQ := BigQ.mul_norm.

Global Instance inv_bigQ : inv bigQ := BigQ.inv_norm.

Global Instance eq_bigQ : eq bigQ := BigQ.eq_bool.

End operations.
