Add LoadPath "../".

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq ssralg.
Require Import Zinfra winograd seqmatrix.
Require Import NArith ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition mat n := [seq map Z_of_nat (iota x n) | x <- iota 1 n].

(* Size 10x10 *)
Definition m10 := mat 10.

Time Eval vm_compute in mulseqmx m10 m10.
Time Eval vm_compute in winograd_peelingI Z_ringType (P_of_succ_nat (size m10)) m10 m10.


(* Size 50x50 *)
Definition m50 := mat 50.

Time Eval vm_compute in mulseqmx m50 m50.
Time Eval vm_compute in winograd_peelingI Z_ringType (P_of_succ_nat (size m50)) m50 m50.


(* Size 100x100 *)
Definition m100 := mat 100.

Time Eval vm_compute in mulseqmx m100 m100.
Time Eval vm_compute in winograd_peelingI Z_ringType (P_of_succ_nat (size m100)) m100 m100.
