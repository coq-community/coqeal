Add LoadPath "../".

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg bigop.
Require Import cssralg.
Require Import QArith_base Qcanon Qinfra.

Close Scope Q_scope.

Notation "n %:Q" := (n%Z : Qcb) (at level 2, left associativity, format "n %:Q").

Eval compute in (add 3%:Q 4%:Q).
Eval compute in (mul 3%:Q 4%:Q).

Eval compute in (cunit 4%:Q).
Eval compute in (cinv 4%:Q).
