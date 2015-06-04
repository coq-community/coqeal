Require Import Parametricity.

Parametricity StartProof (fun (X : Type) (x : X) (f : ((fix f (n : nat) := X -> X) _)) => _ _)  (forall X, X -> (X -> X) -> X).
exact 0.
exact f.
exact x.
Defined.

Fixpoint f (n : nat) := 0.

Definition eq_f : forall n, f n = 0.
intro n; destruct n; reflexivity.
Defined.

Print eq_f.

Set Parametricity Program.

Require Import Program.
Set Printing All.
Set Parametricity Debug.
Print eq_f.
Parametricity eq_f.
Print eq_f_R.

Program Definition test := 
fun (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) =>
match
  n_R as n_R0 in (nat_R n₁0 n₂0)
  return
    (eq_R nat nat nat_R (f n₁0) (f n₂0)
       ((let fix_f_1 := fix f (n : nat) : nat := 0 in
         let fix_f_2 := fix f (n : nat) : nat := 0 in
         fix f_R (n₁1 n₂1 : nat) (n_R1 : nat_R n₁1 n₂1) {struct n_R1} : 
         nat_R (fix_f_1 n₁1) (fix_f_2 n₂1) :=
           let gen_path := _ in
           eq_rect 0 (fun x : nat => nat_R x (fix_f_2 n₂1))
             (eq_rect 0 (fun x : nat => nat_R 0 x) O_R (fix_f_2 n₂1) (gen_path n₂1)) 
             (fix_f_1 n₁1) (gen_path n₁1)) n₁0 n₂0 n_R0) 0 0 O_R
       match n₁0 as n return (f n = 0) with
       | 0 => eq_refl
       | S _ => eq_refl
       end match n₂0 as n return (f n = 0) with
           | 0 => eq_refl
           | S _ => eq_refl
           end)
with
| O_R => eq_refl_R nat nat nat_R 0 0 O_R
| S_R _ _ _ => eq_refl_R nat nat nat_R 0 0 O_R
end 
.
Next Obligation. destruct_reflexivity. Defined.
Print test.





Program Definition test (X : nat -> nat -> Type) (x : X 1 1) : X 0 1 := x.
Next Obligation.
admit.
Defined.
Print test. 
  
 
 
