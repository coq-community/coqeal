Add LoadPath "../".

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
Require Import dvdring cssralg Zinfra.
Require Import Coq.ZArith.Zdiv Coq.ZArith.Zabs.
Import ssrnat ssralg.


Time Eval compute in (3 %| 4)%Z.
Time Eval compute in (2342 %/ 123)%Z.
Time Eval compute in (123123 %/ 1234)%Z.

Time Eval compute in (gcdr 6685 4011)%Z.
Time Eval compute in (GCD 6685 4011)%Z.
Time Eval compute in (gcdr 11466 1428)%Z.
Time Eval compute in (GCD 11466 1428)%Z.
Time Eval compute in (gcdr 114662 14282)%Z.
Time Eval compute in (GCD 114662 14282)%Z.

Eval compute in (mul 3%Z 4%Z).
Eval compute in (mul 3%Z 4%Z).

Eval compute in (cunit 4%Z).
Eval compute in (cinv 1%Z).