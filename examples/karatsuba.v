Add LoadPath ".." as CoqEAL.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg bigop poly.
Require Import refinements karatsuba.

Require Import binnat binint seqpoly.

Section computable.

Local Open Scope computable_scope.
Local Notation N := BinNums.N.
Local Notation Z := (Z N N).

Definition karatsubaZ : seqpoly Z -> seqpoly Z -> seqpoly Z :=
  karatsuba (@shift Z _) (@size_seqpoly _ _ _) (@split_seqpoly _).

Definition karatsuba_normZ : seqpoly Z -> seqpoly Z -> seqpoly Z :=
  karatsuba_norm (@drop_zero _ _ _) (@shift Z _) (@size _) (@split_seqpoly _).

(* Degree 1000 *)
Definition p1000 : seqpoly Z :=
  Eval vm_compute in map (embed \o bin_of_nat) (iota 1 1000).

(* Time Eval vm_compute in size_seqpoly (p1000 * p1000). *)
Time Eval vm_compute in size_seqpoly (karatsubaZ p1000 p1000).
Time Eval vm_compute in size_seqpoly (karatsuba_normZ p1000 p1000).

(* Degree 2000 *)
Definition p2000 : seqpoly Z :=
  Eval vm_compute in map (embed \o bin_of_nat) (iota 1 2000).

Time Eval vm_compute in size_seqpoly (p2000 * p2000).
Time Eval vm_compute in size_seqpoly (karatsubaZ p2000 p2000).
Time Eval vm_compute in size_seqpoly (karatsuba_normZ p2000 p2000).

(* Polynomial with 100 zeroes in the end *)
Definition many_zeroes : seqpoly Z := p1000 + shift 1100 0.

Time Eval vm_compute in many_zeroes.
Time Eval vm_compute in size_seqpoly (karatsubaZ many_zeroes many_zeroes).
Time Eval vm_compute in size_seqpoly (karatsuba_normZ many_zeroes many_zeroes).

(* First half is positive and second half negative so that they cancel *)
Definition pos_neg : seqpoly Z := p2000 + shift 2000 (- p2000).

Time Eval vm_compute in split_seqpoly 2000 pos_neg.
Time Eval vm_compute in size_seqpoly (karatsubaZ pos_neg pos_neg).
Time Eval vm_compute in size_seqpoly (karatsuba_normZ pos_neg pos_neg).

End computable.