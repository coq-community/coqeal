
Declare ML Module "relations".
Declare ML Module "parametricity".
Declare ML Module "declare_translation".
Declare ML Module "abstraction".

Set Printing All.
Set Printing Universes.

Require Import ProofIrrelevance.
Require CRelationClasses.

Require Relation_Definitions Relation_Operators.



Translate Module Logic.
Next Obligation.
admit.
Defined.

Translate Module Datatypes.


Translate Module Relation_Definitions.
Translate Module Logic_Type.
Translate Module Specif.

Check Relation_Operators.Ltl_ind.

Import Datatypes_R.

Check (list_R nat nat nat_R).

Check Relation_Operators.Ltl.

Translate Module Relation_Operators.


Translate Module Nat.
Translate Module Peano.

Translate Module Wf.

Require Bool Basics Init Tactics Relation_Definitions RelationClasses Morphisms CRelationClasses.

Translate Module Bool.
Translate Module Basics.
Translate Module Init.
Translate Module Tactics.

Translate Module CRelationClasses.

Next Obligation. (* StrictOrder_Asymmetric *)
admit.
Defined.

Next Obligation. (* subrelation_symmetric *)
admit.
Defined.

Next Obligation. (* flip_Reflexive *)
admit.
Defined.

Next Obligation. (* flip_Antisymmetric *)
admit.
Defined.

Next Obligation. (* flip_PreOrder *)
admit.
Defined.

Next Obligation. (* flip_StrictOrder *)
admit.
Defined.

Next Obligation. (* flip_PER *)
admit.
Defined.

Next Obligation. (* flip_Equivalence *)
admit.
Defined.

Next Obligation. (* complement_Irreflexive *)
admit.
Defined.

Next Obligation. (* complement_Symmetric *)
admit.
Defined.

Next Obligation. (* relation_equivalence_equivalence *)
admit.
Defined.

Next Obligation. (* relation_implication_preorder_R *)
admit.
Defined.

Next Obligation. (* partial_order_antisym *)
admit.
Defined.

Next Obligation. (* PartialOrder_inverse *)
admit.
Defined.


Translate Module RelationClasses.
Translate Module Morphisms.

Require CMorphisms Morphisms_Prop Equivalence SetoidTactics Setoid Equalities Relation_Operators Operators_Properties Relations Orders NumPrelude OrdersTac OrdersFacts GenericMinMax NZAxioms NZBase NZAdd NZMul Decidable NZOrder NZAddOrder NZMulOrder NZParity NZPow NZSqrt NZLog NZDiv NZGcd NZBits NAxioms NZProperties NBase NAdd NOrder NAddOrder NMulOrder NSub NMaxMin NParity NPow NSqrt NLog NDiv NGcd NLcm NBits NProperties.


Translate Module CMorphisms.

Next Obligation. (* reflexive_proper_proxy *)
admit.
Defined.

Next Obligation. (* proper_proper_proxy *)
admit.
Defined.
Next Obligation. (* pointwise_pointwise *)
admit.
Defined.
Next Obligation. (* subrelation_id_proper *)
admit.
Defined.
Next Obligation. (* subrelation_respectful *)
admit.
Defined.
Next Obligation. (* subrelation_refl *)
admit.
Defined.
Next Obligation. (* subrelation_proper *)
admit.
Defined.
Next Obligation. (* subrelation_proper_arrow *)
admit.
Defined.
Next Obligation. (* pointwise_subrelation *)
admit.
Defined.
Next Obligation. (* forall_subrelation *)
admit.
Defined.
Next Obligation. (* iff_impl_subrelation *)
admit.
Defined.
Next Obligation. (* iff_flip_impl_subrelation *)
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.

Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.

Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.

Require Equivalence PeanoNat Le Lt Plus Gt Minus List.

Translate Module Equivalence.
Translate Module Morphisms_Prop.

Translate Module SetoidTactics.
Translate Module Setoid.
Translate Module Equalities.

Translate Module Operators_Properties.
Translate Module Relations.
Translate Module Orders.
Translate Module NumPrelude.
Translate Module OrdersTac.
Translate Module OrdersFacts.
Translate Module GenericMinMax.
Translate Module NZAxioms.
Translate Module NZBase.
Translate Module NZAdd.
Translate Module NZMul.
Translate Module Decidable.

(*
Translate Module NZOrder.
Translate Module NZAddOrder.
Translate Module NZMulOrder.
Translate Module NZParity.
Translate Module NZPow.
Translate Module NZSqrt.
Translate Module NZLog.
Translate Module NZDiv.
Translate Module NZGcd.
Translate Module NZBits.
Translate Module NAxioms.
Translate Module NZProperties.
Translate Module NBase.
Translate Module NAdd.
Translate Module NOrder.
Translate Module NAddOrder.
Translate Module NMulOrder.
Translate Module NSub.
Translate Module NMaxMin.
Translate Module NParity.
Translate Module NPow.
Translate Module NSqrt.
Translate Module NLog.
Translate Module NDiv.
Translate Module NGcd.
Translate Module NLcm.
Translate Module NBits.
Translate Module NProperties.
*)



Translate Module PeanoNat.

Translate Module Le.
Translate Module Lt. 
Translate Module Plus.
Translate Module Gt.
Translate Module Minus.
Translate Module List.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Require Permut Multiset Omega Relations_1 Sorted SetoidList Compare_dec EqNat ListDec Mult Between EqdepFacts Eqdep_dec Peano_dec Factorial Wf_nat Arith_base Fin FinFun Permutation PermutSetoid Mergesort Sorting Heap.
Translate Module Permut. 
Translate Module Multiset.
Translate Module Omega.
Translate Module Relations_1.
Translate Module Sorted.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Translate Module SetoidList.
Translate Module Compare_dec.
Translate Module EqNat.
Translate Module ListDec.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Translate Module Mult.
Translate Module Between.
Translate Module EqdepFacts.
Translate Module Eqdep_dec.
Translate Module Peano_dec.
Translate Module Factorial.
Translate Module Wf_nat.
Translate Module Arith_base.
Translate Module Fin.
Next Obligation.
admit. (* provable *)
Defined.
Next Obligation.
destruct p; reflexivity.
Defined.
Next Obligation.
destruct o; reflexivity.
Defined.
Next Obligation.
destruct p; reflexivity.
Defined.

Translate Module FinFun.

Translate Module Permutation.

Translate Module BinNums.

Translate Module BinPosDef.

Print Module BinPosDef.Pos.


Print BinPosDef_R.Pos_R.

Print PArith.BinPos.Pos.SubMaskSpec.
(* PArith.BinPos.Pos.SubMaskSpec *)
(*
Translate Module PermutSetoid.
Translate Module MergeSort. 
Translate Module Sorting.
Translate Module Heap.
*)
