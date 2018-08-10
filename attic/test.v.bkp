(* Implicit Types tr : bool. *)
(* Require Import Classes.Init. *)
(* Class try (A : Type) := Try : A. *)
(* Class auto_conj A B := AutoConj {auto_proj1 :> try A; auto_proj2 :> try B}. *)
(* Hint Extern 100 =>   *)
(*   match goal with |- try _ => shelve | _ => class_apply Try  end : typeclass_instances. *)

Class a1 tr := A1 {}.
Class a2 tr := A2 {}.

(* Goal auto_conj (a1 true) (a2 true) -> False. *)
(* intro. *)
(* assert (a1 true). *)
(*   typeclasses eauto. *)

Class a3 tr := A3 {}.

Class b1 tr := B1 {}.
Class b2 tr := B2 {}.

Class a tr := a12a { a1a :> a1 false; a2a :> a2 false}.
Instance a12a_tr tr : a1 true -> a2 true -> a tr. 

Class a' tr := aa3a {aa' :> a false; a3a' : a3 false}.
Instance aa3a_tr tr : a true -> a3 true -> a tr. 

Axiom b12a : forall tr, b1 true -> b2 true -> a' tr.
Axiom ab1 : forall tr, a' tr -> b1 false.
Axiom ab2 : forall tr, a' tr -> b2 false.
Existing Instances (* b12a *) ab1 ab2.

Lemma test `{x1 : b1 true} `{x2 : b2 true} : a false.
Set Typeclasses Debug.
typeclasses eauto.


Fixpoint prime n :=
  let fix dvdn k := match k with
                  1 => true
                | S k => match Nat.compare (Nat.modulo n (S k)) 0 with
                           Eq => false
                         |_ => dvdn k end
                | _ => false
                    end
  in match n with S n => dvdn n | _ => false end.

Class is_prime n := SolvePrime : prime n = true.
Hint Extern 0 (is_prime _) =>
  vm_compute; reflexivity : typeclass_instances.

Lemma solve_prime n `{is_prime n} : prime n = true.
Proof. exact H. Qed.

Goal (prime 4049 = true).
time compute.