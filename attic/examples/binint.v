(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.
Require Import refinements pos binint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**************************************************************************)
(* We create a separate tests file because there is no other way to       *)
(* delimit instance scopes than having a "file-based import".  Indeed, if *)
(* we "Require binnat" directly in binint, then we get the binnat         *)
(* refinements forever.                                                   *)
(**************************************************************************)
Require binnat.
(* now we have binnat refinements in this file, with no possible change *)


Section BinInt.

Import Refinements.
Open Scope ring_scope.

Lemma test : 10000%num%:Z * 10000%num%:Z =
             100000000%num%:Z :> int.
Proof. by apply/eqP; rewrite [(_ == _)]param_eq. Qed.

Lemma test' : 10000%num%:Z * 10000%num%:Z * (99999999%num%:Z + 1) =
             10000000000000000%num%:Z :> int.
Proof. by apply/eqP; rewrite [(_ == _)]param_eq. Qed.

Lemma test'' : 10000%num%:Z * 10000%num%:Z * (99999999%num%:Z + 1) =
             10000000000000000%num%:Z :> int.
Proof.
rewrite -[X in X = _]specE.
set a := (X in Op.spec X); vm_compute in a.
(* we should make specZ locked somehow *)
done.
Qed.

End BinInt.
