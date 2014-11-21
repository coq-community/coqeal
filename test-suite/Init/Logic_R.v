Require Import Parametricity. 
Require Import ProofIrrelevance.

(** Logic.v **)
Translate Inductive True.
Translate Inductive False. 



Realizer proof_admitted as proof_admitted_R := _.
Next Obligation.
destruct proof_admitted.
Defined.
Translate not. 
Translate Inductive and. 
Translate Inductive or. 
Translate Inductive ex.
Translate Inductive ex2.
Translate iff.
Translate IF_then_else.
Translate all. 

Translate Inductive eq.

Translate eq_sym.
Translate eq_trans. 

Translate eq_ind_r. 
Translate eq_rec_r. 
Translate eq_rect_r. 
Translate rew_opp_r. 
Translate rew_opp_l.

Translate f_equal. 
Translate f_equal2.
Translate f_equal3.
Translate f_equal4.
Translate f_equal5. 
Translate f_equal_compose. 
Translate eq_trans_refl_l. 
Translate eq_trans_refl_r. 
Translate eq_sym_involutive.
Translate eq_trans_sym_inv_l. 
Translate eq_trans_sym_inv_r. 
Translate eq_trans_assoc.
Translate eq_id_comm_l.
Translate eq_id_comm_r. 
Translate eq_trans_map_distr.
Translate eq_sym_map_distr.
Translate eq_trans_sym_distr.

Translate subrelation.
Translate unique.
Translate uniqueness.

Translate Inductive inhabited. 

(* Opaque definitions : *)

Translate proj1.
Translate proj2. 

Translate iff_refl.
Translate iff_trans.
Translate iff_sym.

Translate and_iff_compat_l.
Translate and_iff_compat_r.
Translate or_iff_compat_l.
Translate or_iff_compat_r.

Translate neg_false.
Translate and_cancel_l.
Translate and_cancel_r.
Translate and_comm.
Translate and_assoc.
Translate or_cancel_l.
Translate or_cancel_r.
Translate or_comm.
Translate or_assoc.
Translate iff_and.
Translate iff_to_and.

Translate inst.
Translate gen.

Translate absurd.
Translate not_eq_sym.
Translate unique_existence.
Translate forall_exists_unique_domain_coincide.
Translate forall_exists_coincide_unique_domain.       
Translate exists_inhabited.
Translate eq_stepl.
Translate iff_stepl.

