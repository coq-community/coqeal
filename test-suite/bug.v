Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "declare_translation".
Declare ML Module "abstraction".

Translate Inductive nat.

Section Truc.
Variable m : nat.
Fixpoint f (n : nat) := match n with 0 => m | S p => f p end.
End Truc.

Translate f.

Print nat_rect.

Translate nat_rect.

Inductive even : nat -> Type :=
 | even_zero : even 0
 | even_succ : forall n, odd n -> even (S n)
with odd : nat -> Type :=
 | odd_succ : forall n, even n -> odd (S n).

Fixpoint size_even n (H : even n) := 
  match H with 
    | even_zero => 0
    | even_succ n p => S (size_odd _ p)
   end 
with size_odd n H := 
   match H with 
     | odd_succ n p => S (size_even _ p)
   end.

Translate Inductive even.
Translate size_even.

Print size_even_R.
Check size_even_R.

(*

Print list.

Inductive zero : Type :=
   zero_zero : zero
 | zero_one : one -> zero
 | zero_two : two -> zero
with one : Type :=
 | one_zero : zero -> one
 | one_one : one
 | one_two : two -> one
with two : Type :=
 | two_zero : zero -> two
 | two_one : one -> two
 | two_two : two.

Translate Inductive zero.

Fixpoint f_zero (z : zero) : nat :=
  match z with 
   | zero_zero => 0
   | zero_one x => f_one x
   | zero_two x => f_two x 
  end 
with f_one (z : one) : nat :=
  match z with 
   | one_zero x => f_zero x
   | one_one => 1
   | one_two x => f_two x 
  end
with f_two (z : two) : nat :=
  match z with 
   | two_zero x => f_zero x
   | two_one x => f_one x
   | two_two => 2
  end.
Translate Inductive nat.
Translate f_zero.
Check zero_R.
Check one_R.
*)
