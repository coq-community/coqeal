(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice fintype.
Require Import tuple finfun bigop finset binomial fingroup perm hrel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cperm_def.

Definition funperm := nat -> nat.

Definition funperm_of_perm n : 'S_n -> funperm :=
  if n is _.+1 return 'S_n -> (nat -> nat) then fun s k => s (inord k)
  else fun _ => id.

Definition finfun_of_funperm n f : {ffun ('I_n.+1 -> 'I_n.+1)} :=
  [ffun k => inord (f k)].
  
(* Magie à méditer : *)
(* case: {-}_ / idP. *)
(* cf insubP dans eqtype.v *)


Definition perm_of_funperm n (f : funperm) : option 'S_n :=
  if n is n'.+1 return option 'S_n then insub (@finfun_of_funperm n' f)
  else Some 1%g.
 
Lemma funperm_of_permK n : pcancel (@funperm_of_perm n) (@perm_of_funperm n).
Proof.
case: n => [|n] s; first by congr Some; apply/permP; case.
rewrite /= insubT => [|?].
  by apply/injectiveP=> k l; rewrite !ffunE !inord_val; apply: perm_inj.
congr Some; apply/permP=> k.
by rewrite {1}PermDef.fun_of_permE ffunE !inord_val.
Qed.

Definition Rfunperm {n} := ofun_hrel (perm_of_funperm n).

(* Global Instance refinement_perm_funperm n : *)
(*   refinement _ := Refinement (@Rfunperm n). *)

Definition ctperm (i j k : nat) :=
  if i == k then j else if j == k then i else k.

Definition cperm_comp (s t : nat -> nat) := s \o t.

Definition lift0_cperm (s : nat -> nat) k :=
  if k is l.+1 then (s l).+1 else 0.

End cperm_def.
