
Require Import Parametricity.


Fixpoint pred (n : nat) := 
  match n with 
   | 0 => 0 
   | S p => id p
  end
with id (n : nat) :=
   match n with 
    | 0 => 0
    | S p => S (pred p)
   end.

DebugTranslation pred.