Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice fintype.
Require Import tuple finfun bigop finset binomial fingroup perm.

Section cperm_def.

Variable n' : nat.
Local Notation n := n'.+1.

Definition cperm_of_perm (s : 'S_n) k := s (inord k) : nat.

Definition ctperm (i j k : nat) :=
  if i == k then j else if j == k then i else k.

Definition cperm_comp (s t : nat -> nat) := s \o t.

Definition lift0_cperm (s : nat -> nat) k :=
  if k is l.+1 then (s l).+1 else 0.

End cperm_def.