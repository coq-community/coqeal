Require Import Parametricity.

(** Base Types. **)

Inductive bool := true | false.

Translate Inductive bool.

Print bool_R.
(* Prints:  
Inductive bool_R : bool -> bool -> Set :=  
  true_R : bool_R true true 
| false_R : bool_R false false *)

Lemma bool_R_eq:
  forall x y, bool_R x y -> x = y.
intros x y H.
destruct H.
* reflexivity.
* reflexivity.
Defined.

Lemma bool_R_refl:
   forall x, bool_R x x.
induction x.
constructor.
constructor.
Defined.

(** Boolean functions **)

Definition boolfun := bool -> bool.
Translate boolfun.
Print boolfun_R.
(* Prints:
boolfun_R = fun f1 f2 : bool -> bool => 
   forall x1 x2 : bool, bool_R x1 x2 -> 
                        bool_R (f1 x1) (f2 x2)
*)

Print Module Bool.

Definition negb (x : bool) := 
  match x with 
   | true => false
   | fale => true
  end. 
Translate negb.
Check negb_R.
Print negb_R.

(** Universes **)

Translate Type as Type_R.
Print Type_R.
(* Prints : 
  Type_R = fun A1 A2 : Type => A1 -> A2 -> Type
*)
Check (bool_R : Type_R bool bool).
Check (boolfun_R : Type_R boolfun boolfun).

Polymorphic Definition pType := Type.
Translate pType.
Check (pType_R : pType_R pType pType).

(** Simple arrows **)

Definition arrow (A : Type) (B  : Type) := 
  A -> B.

Translate arrow.
Print arrow_R.
(* Prints: 
arrow_R = 
  fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) 
      (B₁ B₂ : Type) (B_R : B₁ -> B₂ -> Type) 
      (f₁ : A₁ -> B₁) (f₂ : A₂ -> B₂) =>
  forall (x₁ : A₁) (x₂ : A₂), 
    A_R x₁ x₂ -> B_R (f₁ x₁) (f₂ x₂)
*)

(** Lambdas **)
Definition lambda (A : Type) (B : Type)
  (f : arrow A B) := fun x => f x.
Translate lambda.
Print lambda_R.
(* lambda_R = 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
    (B₁ B₂ : Type) (B_R : B₁ -> B₂ -> Type) 
  (f₁ : arrow A₁ B₁) (f₂ : arrow A₂ B₂) 
     (f_R : arrow_R A₁ A₂ A_R B₁ B₂ B_R f₁ f₂) 
  (x₁ : A₁) (x₂ : A₂) (x_R : A_R x₁ x₂) => f_R x₁ x₂ x_R *)

(** Applications of functions *)
Definition application A B (f : arrow A B) (x : A) : B :=
  f x.
Translate application.
Print application_R.
(* Prints : 
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) 
    (B₁ B₂ : Type) (B_R : B₁ -> B₂ -> Type) 
    (f₁ : arrow A₁ B₁) (f₂ : arrow A₂ B₂) 
          (f_R : arrow_R A₁ A₂ A_R B₁ B₂ B_R f₁ f₂) 
    (x₁ : A₁) (x₂ : A₂) (x_R : A_R x₁ x₂) => f_R x₁ x₂ x_R. *)

(** Dependent product **)
Definition for_all (A : Type) (B : A -> Type) := forall x, B x.
Translate for_all.
Print for_all_R.
(* Prints: 
for_all_R =
fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) 
    (B₁ : A₁ -> Type) (B₂ : A₂ -> Type) 
    (B_R : forall (x₁ : A₁) (x₂ : A₂), A_R x₁ x₂ -> B₁ x₁ -> B₂ x₂ -> Type) 
    (f₁ : forall x : A₁, B₁ x) (f₂ : forall x : A₂, B₂ x) => 
for all (x₁ : A₁) (x₂ : A₂) (x_R : A_R x₁ x₂), B_R x₁ x₂ x_R (f₁ x₁) (f₂ x₂)
*)

(** Inductive types. *)
Inductive nat := 
  | O : nat 
  | S : nat -> nat.
Translate Inductive nat.
Print nat_R.
(* Prints:
Inductive nat_R : nat -> nat -> Set :=  
  O_R : nat_R 0 0 
| S_R : forall n₁ n₂ : nat, nat_R n₁ n₂ -> nat_R (S n₁) (S n₂) *)

Inductive list (A : Type) : Type :=  nil : list A | cons : A -> list A -> list A.
Translate Inductive list.
Print list_R.
(* Prints : 
Inductive list_R (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) : 
                                         list A₁ -> list A₂ -> Type :=
    nil_R : list_R A₁ A₂ A_R (nil A₁) (nil A₂)
  | cons_R : forall (x₁ : A₁) (x₂ : A₂), A_R x₁ x₂ -> 
    forall (l₁ : list A₁) (l₂ : list A₂),
    list_R A₁ A₂ A_R l₁ l₂ -> list_R A₁ A₂ A_R (cons A₁ x₁ l₁) (cons A₂ x₂ l₂)
*)

Fixpoint length A (l : list A) : nat := 
  match l with nil _ => O | cons _ _ tl => S (length A tl) end.
Translate length.
Check length_R.
Print length_R.
(* Prints : ... something that looks complicated. *)

Translate list_rec.
Print list_rec_R.
Definition length2 (A : Type) (l : list A) : nat :=
  list_rec A (fun _ => nat) O (fun _ _ => S) l.
Translate length2.
Check length2_R.
Print length2_R.

Print sum_rect.

Translate sum_rect.
Check sum_rect.
Check sum_rect_R.
Print Datatypes_R.sum_rect_R.



