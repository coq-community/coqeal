Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "declare_translation".
Declare ML Module "abstraction".


Require Import ProofIrrelevance. (* for opaque terms *)

Translate Module Logic.

(* Realizer of proof_admitted. *)
Next Obligation.
admit.
Defined.

Translate Module Datatypes.
Translate Module Logic_Type.
Translate Module Specif.
Translate Module Nat.
Translate Module Peano.
Translate Module Wf.
Translate Module Tactics.

Export Logic_R Datatypes_R Logic_Type_R Specif_R Nat_R Peano_R Wf_R Tactics_R.
