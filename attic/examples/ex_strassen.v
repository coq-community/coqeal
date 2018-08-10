Add LoadPath "../".

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq ssralg.
Require Import Zinfra strassen seqmatrix.
Require Import NArith ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition mat n := [seq map Z_of_nat (iota x n) | x <- iota 1 n].

(* Size 25x25 *)
Definition m25 := mat 25.

Time Eval vm_compute in size (mulseqmx 25 25 m25 m25).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m25).-1) m25 m25).


(* Size 50x50 *)
Definition m50 := mat 50.

Time Eval vm_compute in size (mulseqmx 50 50 m50 m50).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m50).-1) m50 m50).


(* Size 75x75 *)
Definition m75 := mat 75.

Time Eval vm_compute in size (mulseqmx 75 75 m75 m75).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m75).-1) m75 m75).


(* Size 100x100 *)
Definition m100 := mat 100.

Time Eval vm_compute in size (mulseqmx 100 100 m100 m100).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m100).-1) m100 m100).


(* Size 125x125 *)
Definition m125 := mat 125.

Time Eval vm_compute in size (mulseqmx 125 125 m125 m125).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m125).-1) m125 m125).


(* Size 150x150 *)
Definition m150 := mat 150.

Time Eval vm_compute in size (mulseqmx 150 150 m150 m150).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m150).-1) m150 m150).


(* Size 175x175 *)
Definition m175 := mat 175.

Time Eval vm_compute in size (mulseqmx 175 175 m175 m175).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m175).-1) m175 m175).


(* Size 200x200 *)
Definition m200 := mat 200.

Time Eval vm_compute in size (mulseqmx 200 200 m200 m200).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m200).-1) m200 m200).


(* Size 225x225 *)
Definition m225 := mat 225.

Time Eval vm_compute in size (mulseqmx 225 225 m225 m225).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m225).-1) m225 m225).


(* Size 250x250 *)
Definition m250 := mat 250.

Time Eval vm_compute in size (mulseqmx 250 250 m250 m250).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType Z_cringType (P_of_succ_nat (size m250).-1) m250 m250).

(*
(* Size 275x275 *)
Definition m275 := mat 275.

Time Eval vm_compute in size (mulseqmx m275 m275).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType (P_of_succ_nat (size m275).-1) m275 m275).


(* Size 300x300 *)
Definition m300 := mat 300.

Time Eval vm_compute in size (mulseqmx m300 m300).
Time Eval vm_compute in size (Strassen_seqmx Z_ringType (P_of_succ_nat (size m300).-1) m300 m300).
*)