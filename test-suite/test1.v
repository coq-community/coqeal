Require Import List.

Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "abstraction".

(** Inductive **)
Translate Inductive nat.
Translate Inductive list.
Translate Inductive option.
Translate Inductive option Arity 1.
Translate Inductive list Arity 1.
Translate Inductive nat Arity 1.
Translate Inductive nat Arity 10.
(** Match with *)
Translate pred.
Translate hd.
Translate pred Arity 10.
(** Fixpoint **)
Translate plus.
Next Obligation. destruct n; reflexivity. Defined.
Translate mult.
Next Obligation. destruct n; reflexivity. Defined.
Translate plus Arity 1.
Next Obligation. destruct n; reflexivity. Defined.
Translate mult Arity 1.
Next Obligation. destruct n; reflexivity. Defined.
Translate plus Arity 10.
Next Obligation. destruct n; reflexivity. Defined.
Translate mult as mult_R_test Arity 10.
Next Obligation. destruct n; reflexivity. Defined.
Check mult_R_test.
