Require Import Parametricity. 
Require Import Logic_R.

Translate Inductive Empty_set.
Translate Inductive unit.
Translate Inductive bool.
Translate andb.
Translate orb.
Translate implb.
Translate xorb.
Translate negb.

Require Import ProofIrrelevance.

Translate andb_prop.
Translate andb_true_intro.


Translate Inductive eq_true.

Translate is_true.

Translate eq_true_ind_r.
Translate eq_true_rec_r.
Translate eq_true_rect_r.

Translate Inductive BoolSpec.

Translate Inductive nat.
Translate Inductive option.

Translate option_map.

Translate Inductive sum.

Translate Inductive prod.

Translate @fst.
Translate @snd.

Translate surjective_pairing.
Translate injective_projections.
Translate prod_uncurry.
Translate prod_curry.

Translate Inductive list.
Translate length.
Translate app.


Translate Inductive comparison.

Translate CompOpp.

Translate CompOpp_involutive.
Translate CompOpp_inj.

Translate CompOpp_iff.

Translate Inductive CompareSpec.
Translate Inductive CompareSpecT.
Translate CompareSpec2Type.
Translate @CompSpec.
Translate @CompSpecT.
Translate CompSpec2Type.

Translate Inductive identity.

Translate ID.
Translate id.

Translate IDProp.
Translate idProp.
