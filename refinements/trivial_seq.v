Require Import ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq zmodp.
From mathcomp Require Import path choice fintype tuple finset ssralg ssrnum bigop ssrint.

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.

Section size_seq.

Context (A : Type) (N : Type) `{zero_of N} `{one_of N} `{add_of N}.

Global Instance size_seq : size_of (seq A) N := 
  fix size xs := if xs is x :: s then (size s + 1)%C else 0%C.

End size_seq.
Parametricity size_seq.

Lemma size_seqE T (s : seq T) : (@size_seq _ _ 0%N 1%N addn) s = size s.
Proof. by elim: s => //= x s ->; rewrite [(_ + _)%C]addn1. Qed.

Section seq_refines.

Local Open Scope rel_scope.

Variable (A C : Type) (rAC : A -> C -> Type).
Variable (N : Type) (rN : nat -> N -> Type).
Context `{implem_of A C} `{spec_of N nat}.
Context `{zero_of N} `{one_of N} `{add_of N}.
Context `{!refines (Logic.eq ==> rAC) implem_id implem}.
Context `{!refines (rN ==> nat_R) spec_id spec}.
Context `{!refines rN 0%N 0%C}.
Context `{!refines rN 1%N 1%C}.
Context `{!refines (rN ==> rN ==> rN) addn add_op}.

Global Instance refine_nth1 :
  refines (rAC ==> list_R rAC ==> rN ==> rAC)
          nth (fun x s (n : N) => nth x s (spec n)).
Proof.
  param nth_R.
  rewrite -[X in refines _ X _]/(spec_id _); exact: refines_apply.
Qed.

Global Instance refine_nth2 :
  refines (list_R (list_R rAC) ==> rN ==> list_R rAC)
          (nth [::]) (fun s (n : N) => nth [::] s (spec n)).
Proof.
  param nth_R.
    rewrite refinesE; exact: list_R_nil_R.
  rewrite -[X in refines _ X _]/(spec_id _); exact: refines_apply.
Qed.

Global Instance refine_list_R2_implem s :
  refines (list_R (list_R rAC)) s (map (map implem) s).
Proof.
  rewrite refinesE.
  elim: s=> [|a s ihs] /=.
    exact: list_R_nil_R.
  apply: list_R_cons_R.
    elim: a=> [|hd tl ih] /=.
      exact: list_R_nil_R.
      apply: list_R_cons_R.
      have heq : refines eq hd hd by rewrite refinesE.
      rewrite -[X in rAC X _]/(implem_id _).
      exact: refinesP.
    exact: ih.
  exact: ihs.
Qed.

Global Instance refine_size : refines (list_R rAC ==> rN) size size_op.
Proof.
by rewrite refinesE => s s' rs; rewrite -[size s]size_seqE; param size_seq_R.
Qed.

End seq_refines.
