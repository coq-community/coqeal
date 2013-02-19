Add LoadPath "..".
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

(* Degree 1000 *)
Definition p1000 : seqpoly Z :=
  Eval vm_compute in map (embed \o bin_of_nat) (iota 1 1000).

Time Eval vm_compute in size_seqpoly (p1000 * p1000).
Time Eval vm_compute in size_seqpoly (karatsubaZ p1000 p1000).


(* Degree 2000 *)
Definition p2000 : seqpoly Z :=
  Eval vm_compute in map (embed \o bin_of_nat) (iota 1 2000).

Time Eval vm_compute in size_seqpoly (mul_op p2000 p2000).
Time Eval vm_compute in size_seqpoly (karatsubaZ p2000 p2000).

End computable.