Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "declare_translation".
Declare ML Module "abstraction".

Global Ltac destruct_reflexivity := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.


Global Parametricity Tactic := destruct_reflexivity. 

Require Import ProofIrrelevance. (* for opaque terms *)

Parametricity Module Logic.
admit.
Parametricity Done.
Parametricity Module Datatypes.


Parametricity Module Logic_Type.
Parametricity Module Nat.

Parametricity Module Specif.
Parametricity Module Peano.

Parametricity Module Wf.
Parametricity Module Tactics.

Export Logic_R Datatypes_R Logic_Type_R Specif_R Nat_R Peano_R Wf_R Tactics_R. 
