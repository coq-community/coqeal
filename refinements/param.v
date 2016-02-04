From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare ML Module "paramcoq".

Global Ltac destruct_reflexivity :=
  intros ; repeat match goal with
  | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

Global Parametricity Tactic := destruct_reflexivity.

Require Import ProofIrrelevance. (* for opaque terms *)

(* data types *)
Parametricity option.
Parametricity unit.
Parametricity bool.
Hint Resolve true_R false_R.
Parametricity nat.
Parametricity list.
Parametricity prod.

(** ssrfun *)
Parametricity simpl_fun.

(** ssrbool *)
Parametricity SimplRel.

(** ssrnat *)
Parametricity subn_rec.
Parametricity subn.
Parametricity addn_rec.
Parametricity addn.
Parametricity eqn.

(* This trick avoids having to apply Parametricity to eqtype structure *)
Opaque eqn subn.
Definition leqn := Eval cbv in leq.
Parametricity leqn.
Realizer leq as leq_R := leqn_R.

(* geq, ltn and gtn use SimplRel, not sure how well they will work in
   proofs... *)
Parametricity geq.
Parametricity ltn.
Parametricity gtn.

Parametricity maxn.
Parametricity minn.
Parametricity iter.
Parametricity iteri.
Parametricity iterop.
Parametricity muln_rec.
Parametricity muln.
Parametricity expn_rec.
Parametricity expn.
Parametricity fact_rec.
Parametricity factorial.
Parametricity odd.
Parametricity double_rec.
Parametricity double.
Parametricity half.

(** seq *)

(* Here we must make the implicit argument in size explicit *)
Parametricity size.

Definition nilp' T (s : seq T) := eqn (size s) 0.
Parametricity nilp'.
Realizer nilp as nilp_R := nilp'_R.

Parametricity ohead.
Parametricity head.
Parametricity behead.
Parametricity ncons.
Parametricity nseq.
Parametricity cat.
Parametricity rcons.
Parametricity last.
Parametricity belast.
Parametricity nth.
Parametricity set_nth.
Parametricity find.
Parametricity filter.
Parametricity count.
Parametricity has.
Parametricity all.
Parametricity drop.
Parametricity take.
Parametricity rot.
Parametricity rotr.
Parametricity catrev.
Parametricity rev.
Parametricity map.
Parametricity pmap.
Parametricity iota.
Parametricity mkseq.
Parametricity foldr.
Parametricity sumn.
Parametricity foldl.
Parametricity pairmap.
Parametricity scanl.
Parametricity zip.
Parametricity unzip1.
Parametricity unzip2.
Parametricity flatten.
Parametricity shape.
Parametricity reshape.
Parametricity allpairs.

