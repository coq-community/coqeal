Require Import Parametricity.

Definition n1 := 3.
Definition n2 := 2.
Definition n3 := 0.

Inductive I1 (p := n1) (q := n2) (n : nat) (r := n) : Type := c1.
Inductive I2 : let p := n2 in Type := c2.
Inductive I3 : Type := c3 : let p := n3 in I3.

Inductive J : I1 n2 -> I2 -> I3 -> Type :=
  | cj : J (c1 n2) c2 c3.
Inductive K : I1 n3 -> I2 -> I3 -> Type := .

Definition T := I1 n2 -> I2 -> I3.
Definition C := c1.

Set Parametricity Debug.

Parametricity Recursive nat.

Parametricity Recursive I1.

