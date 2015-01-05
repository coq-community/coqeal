Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "declare_translation".
Declare ML Module "abstraction".


Require Import ProofIrrelevance.
Require CRelationClasses.
Require Relation_Definitions Relation_Operators.
Require Bool Basics Init Tactics Relation_Definitions RelationClasses Morphisms CRelationClasses.

Translate Module Logic.
Next Obligation.
admit.
Defined.

Translate Module Datatypes.


Translate Module Relation_Definitions.
Translate Module Logic_Type.
Translate Module Specif.
Translate Module Relation_Operators.


Translate Module Nat.
Translate Module Peano.

Translate Module Wf.



Translate Module Bool.
Translate Module Basics.
Translate Module Init.
Translate Module Tactics.

Export Logic_R Datatypes_R Relation_Definitions_R Logic_Type_R Specif_R Relation_Operators_R Nat_R Peano_R Wf_R Bool_R Basics_R Init_R Tactics_R.