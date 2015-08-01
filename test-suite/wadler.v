Declare ML Module "paramcoq".
Require Import List.

Parametricity nat.

Lemma nat_R_equal : 
  forall x y, nat_R x y -> x = y.
intros x y H; induction H; subst; trivial.
Defined.

Lemma equal_nat_R : 
  forall x y, x = y -> nat_R x y.
intros x y H; subst.
induction y; constructor; trivial.
Defined.

Parametricity list.

Definition full_relation {A B} (x : A) (y : B) := True.

Definition same_length {A B} := list_R A B full_relation.

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
Admitted.


Module LengthType.

Definition T := forall X, list X -> nat.
Parametricity T.

Definition FREE_THEOREM (f : T) := 
  forall A l1 l2,  same_length l1 l2 -> f A l1 = f A l2.

Lemma param_length_type : 
  forall f (f_R  : T_R f f), FREE_THEOREM f.
repeat intro.
apply nat_R_equal.
apply (f_R A A (fun _ _ => True)).
assumption.
Qed.

Parametricity length.
Definition length_rev : T := fun A l => length (rev l).

Parametricity Recursive length_rev.
Definition double_length : T := fun A l => length (l ++ l).

Parametricity Recursive double_length.
Definition constant : T := fun A l => 42.
Parametricity constant.

Definition length_free_theorem : FREE_THEOREM length
  := param_length_type length length_R.
Definition double_length_free_theorem : FREE_THEOREM double_length
  := param_length_type double_length double_length_R.
Definition constant_free_theorem : FREE_THEOREM constant
  := param_length_type constant constant_R.

End LengthType.



Definition graph {A B} (f : A -> B) := fun x y => f x = y.

Definition map_rel {A B} (f : A -> B) := 
  list_R A B (graph f).

Lemma map_rel_map A B (f : A -> B) : 
   forall (l : list A), map_rel f l (map f l).
induction l; constructor; compute; auto.
Defined.

Lemma rel_map_map A B (f : A -> B) : 
   forall (l: list A) fl, map_rel f l fl -> fl = map f l.
intros; induction X; unfold graph in *; subst; reflexivity.
Defined.

Module RevType.

Definition T := forall X, list X -> list X.
Parametricity T.

Definition FREE_THEOREM (F : T) := 
 forall A B (f : A -> B) l, 
      F B (map f l) = map f (F A l).

Lemma param_naturality : 
   forall F (F_R : T_R F F), FREE_THEOREM F.
repeat intro.
apply rel_map_map.
apply F_R.
apply map_rel_map.
Defined.

Parametricity rev.

Definition tail : T := fun A l => 
  match l with 
    | nil => nil 
    | hd :: tl => tl
  end.
Parametricity tail.

Definition rev_rev : T := fun A l => rev (rev l).
Parametricity rev_rev.


Definition rev_naturality : FREE_THEOREM rev 
 := param_naturality rev rev_R.
Definition rev_rev_naturality : FREE_THEOREM rev_rev
 := param_naturality rev_rev rev_rev_R.
Definition tail_naturality : FREE_THEOREM tail
 := param_naturality tail tail_R.

End RevType.


Parametricity prod.

Definition prod_map {A B} (f : A -> B) 
                  {A' B'} (f' : A' -> B') :=
           prod_R A B (graph f) A' B' (graph f').

Definition pair {A B} (f : A -> B) {A' B'} (f' : A' -> B') : A * A' -> B * B' := 
  fun c => let (x, x') := c in (f x, f' x').

Lemma pair_prod_map : 
  forall A B (f : A -> B) 
         A' B' (f' : A' -> B') xy xy', 
       graph (pair f f') xy xy' -> prod_map f f' xy xy'.
intros ? ? f ? ? f' [x y] [x' y'].
intro H.
compute in H.
injection H.
intros; subst.
constructor; reflexivity.
Defined.

Lemma prod_map_pair : 
  forall A B (f : A -> B) 
         A' B' (f' : A' -> B') xy xy', 
       prod_map f f' xy xy' -> graph (pair f f') xy xy'.
intros ? ? f ? ? f' [x y] [x' y'].
intro H.
compute in H.
induction H; subst.
reflexivity.
Defined.


Lemma list_R_prod_map A B (f : A -> B) A' B' (f' : A' -> B') l1 l2 :
  list_R _ _ (prod_map f f') l1 l2 -> list_R _ _ (graph (pair f f')) l1 l2.
intro H; induction H; constructor; [ apply prod_map_pair|]; auto.
Defined.

Module ZipType.

Definition T := 
  forall X Y, list X -> list Y -> list (X * Y).
Parametricity T.

Definition FREE_THEOREM (F : T) := forall
     A B (f : A -> B)
     A' B' (f' : A' -> B') l l', 
      F B B' (map f l) (map f' l') = map (pair f f') (F A A' l l').

Lemma param_ZIP_naturality : 
   forall F (F_R : T_R F F), FREE_THEOREM F.
repeat intro.
specialize (F_R A B (graph f) A' B' (graph f') l (map f l) (map_rel_map _ _ _ _) l' (map f' l') (map_rel_map _ _ _ _)).
apply rel_map_map.
unfold map_rel.
apply list_R_prod_map.
unfold prod_map.
assumption.
Defined.

Fixpoint zip {X Y} (l1 : list X) (l2 : list Y) : list (X * Y) := 
  match l1, l2 with 
   | nil, _ => nil
   | _, nil => nil
   | x::tl1, y::tl2 => (x,y)::(zip tl1 tl2)
  end.
Parametricity zip.
Definition zip_free_theorem : FREE_THEOREM (@zip) := param_ZIP_naturality _ zip_R.

      





