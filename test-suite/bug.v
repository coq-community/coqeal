Set Printing All.

Require Import Parametricity.

Section S.
Variable x : nat.

Definition open_f g n :=  match n with 0 => x | S p => g p end.

Fixpoint f (n : nat) := open_f f n.

End S.

Translate open_f.

Translate f.


Section test.

Variable x : nat.

Definition open_test test n :=  match n with 0 => x | S p => test p end.
Fixpoint test (n : nat) := open_test test n 
with testo (n : nat) := open_test testo n.

End test.

Translate open_test.
Translate test.
Translate testo.

Print test_R.
