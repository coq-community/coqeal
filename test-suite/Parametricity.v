Declare ML Module "paramcoq".


Ltac destruct_reflexivity := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

Ltac destruct_construct x := 
    (destruct x; [ constructor 1 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 | constructor 3]; auto; fail).

Ltac unfold_cofix := intros; match goal with 
 [ |- _ = ?folded ] =>  
    let x := fresh "x" in 
    let typ := type of folded in 
    (match folded with _ _ => pattern folded | _ => pattern folded at 2 end);
    match goal with [ |- ?P ?x ] => 
    refine (let rebuild : typ -> typ := _ in 
            let path : rebuild folded = folded := _ in  
            eq_rect _ P _ folded path) end; 
    [ intro x ; destruct_construct x; fail 
    | destruct folded; reflexivity
    | reflexivity]; fail
end.

Ltac destruct_with_nat_arg_pattern x :=
  pattern x;
  match type of x with 
   | ?I 0 => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun p => _ p
     | S n => fun _  => unit end q) := _ in gen 0 x)     
   | ?I (S ?n) => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun _  => unit 
     | S n => fun p => _ p end q) := _ in gen (S n) x)
  end; intros m q; destruct q.

Ltac destruct_reflexivity_with_nat_arg_pattern := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct_with_nat_arg_pattern x; reflexivity; fail
  end.
 
Global Parametricity Tactic := ((destruct_reflexivity; fail)
                            || (unfold_cofix; fail) 
                            || (destruct_reflexivity_with_nat_arg_pattern; fail)
                            ||  auto). 


Require Import ProofIrrelevance.


(* for opaque terms 

Parametricity and .
Set Parametricity Debug.
Parametricity and_assoc .
Parametricity and_cancel_l .
Parametricity and_cancel_r .
Parametricity and_comm .
Parametricity and_iff_compat_l .
Parametricity and_iff_compat_r .
Parametricity and_ind .
Parametricity and_rec .
Parametricity and_rect .
Parametricity ex .
Parametricity ex2 .
Parametricity ex2_ind .
Parametricity ex_ind .
Parametricity False .
Parametricity False_ind .
Parametricity False_rec .
Parametricity False_rect .
Parametricity iff .
Parametricity iff_and .
Parametricity iff_refl .
Parametricity iff_sym .
Parametricity iff_to_and .
Parametricity iff_trans .
Parametricity or .
Parametricity or_assoc .
Parametricity or_cancel_l .
Parametricity or_cancel_r .
Parametricity or_comm .
Parametricity or_iff_compat_l .
Parametricity or_iff_compat_r .
Parametricity or_ind .
Parametricity proj1 .
Parametricity proj2 .
Parametricity True .
Parametricity True_ind .
Parametricity True_rec .
Parametricity True_rect .
Parametricity IF_then_else .
Parametricity neg_false .
Parametricity not .
Parametricity all.
Parametricity inst.

*)

Set Parametricity Debug.
Definition two : nat := 1+1.

Polymorphic Inductive prod (A B : Type) : Type :=  pair : A -> B -> prod A B.


Inductive list (A : Set) : Set :=  
| nil : list A 
| cons : A -> list A -> list A.

Inductive listT (A : Type) : Type :=  
| nilT : listT A 
| consT : A -> listT A -> listT A.

Parametricity list.

(*
App(Rel(4),[|Rel(3);Rel(2);Rel(1);App(MutConstruct((Top.list,0),,1),[|Rel(3)|])
;App(MutConstruct((Top.list,0),,1),[|Rel(2)|])
|])

Prod(Anonymous,Rel(3),Prod(Anonymous,Rel(3),Prod(Anonymous,App(Rel(3),[|Rel(2);Rel(1)|])
,Prod(Anonymous,App(MutInd(Top.list,0,),[|Rel(6)|])
,Prod(Anonymous,App(MutInd(Top.list,0,),[|Rel(6)|])
,Prod(Anonymous,App(Rel(9),[|Rel(8);Rel(7);Rel(6);Rel(2);Rel(1)|])
,App(Rel(10),[|Rel(9);Rel(8);Rel(7);App(MutConstruct((Top.list,0),,2),[|Rel(9);Rel(6);Rel(3)|])
;App(MutConstruct((Top.list,0),,2),[|Rel(8);Rel(5);Rel(2)|])
|])
)
*)

Parametricity listT.

(*
App(Rel(4),[|Rel(3);Rel(2);Rel(1);App(MutConstruct((Top.listT,0),,1),[|Rel(3)|])
;App(MutConstruct((Top.listT,0),,1),[|Rel(2)|])
|])

Prod(Anonymous,Rel(3),Prod(Anonymous,Rel(3),Prod(Anonymous,App(Rel(3),[|Rel(2);Rel(1)|])
,Prod(Anonymous,App(MutInd(Top.listT,0,),[|Rel(6)|])
,Prod(Anonymous,App(MutInd(Top.listT,0,),[|Rel(6)|])
,Prod(Anonymous,App(Rel(9),[|Rel(8);Rel(7);Rel(6);Rel(2);Rel(1)|])
,App(Rel(10),[|Rel(9);Rel(8);Rel(7);App(MutConstruct((Top.listT,0),,2),[|Rel(9);Rel(6);Rel(3)|])
;App(MutConstruct((Top.listT,0),,2),[|Rel(8);Rel(5);Rel(2)|])
|])
)
)
)
)
)
)

*)

Parametricity Recursive prod.

Print True.

Parametricity Recursive True.

Print True_R.
Parametricity Recursive nat. 
Print nat_R.


Print unit.

Parametricity unit.
Print unit_R.

Set Parametricity Debug.
Parametricity Recursive list.

Print  list.

(* as always, no context *)
*)
(*
(*
Parametricity Module Logic.

Print Logic.
Parametricity Recursive inst.
Parametricity Recursive gen.


*)



Parametricity Module Logic_Type.
Parametricity Module Nat.

Parametricity Module Specif.
Parametricity Module Peano.

Parametricity Module Wf.
Parametricity Module Tactics.

Export Logic_R Datatypes_R Logic_Type_R Specif_R Nat_R Peano_R Wf_R Tactics_R. 
*)