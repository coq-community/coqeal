Require Import Parametricity.
Require Import List.

Print list_R.

Module Length.

Definition same_length {A B} := 
  list_R A B (fun _ _ => True).
Check same_length.

Lemma same_length_length : 
  forall A B (l1 : list A) (l2 : list B), 
    same_length l1 l2 -> length l1 = length l2.
intros A B l1 l2 H.
induction H; simpl.
reflexivity.
exact (f_equal S IHlist_R).
Qed.

Lemma length_same_length : 
  forall A B (l1 : list A) (l2 : list B),
    length l1 = length l2 -> same_length l1 l2.
admit. (* exercise :) *)
Qed.

Lemma nat_R_equal : 
  forall x y, nat_R x y -> x = y.
intros x y H; induction H; subst; trivial.
Defined.

Lemma equal_nat_R : 
  forall x y, x = y -> nat_R x y.
intros x y H; subst.
induction y; constructor; trivial.
Defined.

Definition T := forall X, list X -> nat.
Parametricity T.

Lemma param_length_type : 
  forall f (f_R  : T_R f f) A l1 l2,
    same_length l1 l2 -> f A l1 = f A l2.
intros.
apply nat_R_equal.
apply (f_R A A (fun _ _ => True)).
assumption.
Qed.

Definition f A (l : list A) := 
  length (l ++ l).
Parametricity f.
End Length.


Module Map.

Definition map_rel {A B} (f : A -> B) := 
  list_R A B (fun x y => f x = y).

Lemma map_rel_map A B (f : A -> B) : 
   forall (l : list A), map_rel f l (map f l).
induction l; constructor; auto.
Defined.

Lemma rel_map_map A B (f : A -> B) : 
   forall (l: list A) fl, map_rel f l fl -> fl = map f l.
intros.
induction X; subst; reflexivity. 
Defined.

Definition T := forall X, list X -> list X.

Parametricity T.

Lemma param_naturality : 
   forall F (F_R : T_R F F) 
     A B (f : A -> B) l, 
      F B (map f l) = map f (F A l).
intros.
apply rel_map_map.
apply F_R.
apply map_rel_map.
Defined.

Parametricity rev.

Lemma rev_naturality : 
   forall A B (f : A -> B) l, rev (map f l) = map f (rev l).
apply param_naturality.
apply (rev_R : T_R rev rev).
Defined.

End Map.






