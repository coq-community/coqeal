(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import Int31 Int31Native Streams.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope int31_scope.

Definition ignore {T: Type} (x : T) := tt.

CoFixpoint rand (seed n1 n2 : int) : Stream int :=
   let seed' := Int31Native.mod seed n2 in Streams.Cons seed' (rand (seed' * n1) n1 n2).

Fixpoint random_seq {T : Type} (world : Stream T) (accu : seq T) (n : nat) :=
  match n with
  | O => (accu, world)
  | S p => match world with Streams.Cons x tl => random_seq tl (x :: accu) p end
  end.

Fixpoint random_mx_rec {T: Type} (world : Stream T) (s : seq (seq T)) (m n : nat) :=
  match m with
  | O => (s, world)
  | S p => let: (x, world) := random_seq world [::] n in random_mx_rec world (x :: s) p n
  end.

Definition random_mx (m n : nat) := random_mx_rec (rand 943876 3571 1009) [::] m n.

Definition even (x : int) := Int31Native.eqb (Int31Native.mod x 2) 0.

Definition random_mx_bool (m n : nat) := map (map even) (random_mx m n).1.
