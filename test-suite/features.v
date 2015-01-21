Require Import Parametricity.


(** Separate compilation: *)
Translate nat as test.
Require List.
Translate List.rev.
Check rev_R.

(** Module translation *)
Module A.
  Definition t := nat.
  Module B.
   Definition t := nat -> nat.
  End B.
End A.

Translate Module A.
Print Module A_R.
Print Module A_R.B_R.

Translate Module Bool.
Print Module Bool_R.

(** Unary parametricity *)
Translate (forall X, X -> X) as ID_R arity 1.

Lemma ID_unique: 
  forall f, ID_R f -> forall A x, f A x = x.
intros f f_R A x.
specialize (f_R A (fun y => y = x) x).
apply f_R.
reflexivity.
Defined.

Translate Inductive nat arity 10.
Print nat_R_10.

(** Realizing axioms and section variables. *)
Section Test.
Variable A : Set.
Variable R : A -> A -> Set.
Realizer A as A_R := R.
Definition id : A -> A := fun x => x.
Translate id.
End Test.

Realizer proof_admitted as proof_admitted_R := _.
Next Obligation.
admit.
Defined.

Lemma test_admit: 2+2 = 5.
admit.
Defined.
Translate test_admit.
Print test_admit_R.

(** Opaque terms. **)

Require ProofIrrelevance.

Lemma opaque : True.
trivial.
Qed.
Translate opaque.
Eval compute in opaque.
Eval compute in opaque_R.


Lemma opaquenat : nat.
exact 41.
Qed.
Translate opaquenat.
Next Obligation.
admit.
Defined.


 