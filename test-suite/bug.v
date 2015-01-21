Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "declare_translation".
Declare ML Module "abstraction".

Module False.

Inductive False := .

Axiom admit : False.

Definition test := forall X, X.

End False.

Translate Module False.

Next Obligation.
destruct False.admit.
Defined.

Print Module False_R.

