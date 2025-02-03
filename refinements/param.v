From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From elpi Require Import derive param2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[global] Ltac destruct_reflexivity :=
  intros ; repeat match goal with
  | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

(** Automation: for turning [sth_R a b] goals into mere [a = b] goals,
do [suff_eq sth_Rxx]. *)
Ltac suff_eq Rxx :=
  match goal with
  | [ |- ?R ?a ?b ] =>
    let H := fresh in
    suff H : a = b; first (rewrite H; eapply Rxx =>//)
  end.

Require Import ProofIrrelevance. (* for opaque terms *)

(* data types *)
Elpi derive.param2 option.
Elpi derive.param2 unit.
Elpi derive.param2 bool.
#[export] Hint Resolve true_R false_R : core.
Elpi derive.param2 nat.
Elpi derive.param2 list.
Elpi derive.param2 prod.

Lemma bool_Rxx b : bool_R b b.
Proof. by case: b. Qed.

Lemma nat_Rxx n : nat_R n n.
Proof.
  elim: n=> [|n];
    [ exact: O_R | exact: S_R ].
Qed.

Lemma list_Rxx T (rT : T -> T -> Type) l :
  (forall x, rT x x) -> list_R rT l l.
Proof.
move=> Hr; elim: l=> [|h t IH]; [exact: nil_R|].
exact: cons_R.
Qed.

Lemma option_Rxx T (rT : T -> T -> Type) l :
  (forall x, rT x x) -> option_R rT l l.
Proof. by move=> Hr; case: l => *; constructor. Qed.

(** ssrfun *)
Elpi derive.param2 simpl_fun.

(** ssrbool *)
Elpi derive.param2 pred.
Elpi derive.param2 rel.
Elpi derive.param2 simpl_pred.
Elpi derive.param2 simpl_rel.
Elpi derive.param2 SimplPred.
Elpi derive.param2 SimplRel.
Elpi derive.param2 orb.
Elpi derive.param2 andb.
Elpi derive.param2 implb.
Elpi derive.param2 negb.
Elpi derive.param2 addb.
Elpi derive.param2 eqb.

(** ssrnat *)
Elpi derive.param2 Nat.sub.
Elpi derive.param2 subn.
Elpi derive.param2 subn_rec.
Elpi derive.param2 Nat.add.
Elpi derive.param2 addn.
Elpi derive.param2 addn_rec.
Elpi derive.param2 addn.
Elpi derive.param2 eqn.

(* This trick avoids having to apply Parametricity to eqtype structure *)
Opaque eqn subn.
Definition leqn := Eval cbv in leq.
Elpi derive.param2 leqn.
Definition leq_R := leqn_R.
Elpi derive.param2.register leq leq_R.

Elpi derive.param2 Logic.eq.

(* geq, ltn and gtn use SimplRel, not sure how well they will work in
   proofs... *)
Elpi derive.param2 geq.
Elpi derive.param2 ltn.
Elpi derive.param2 gtn.

Elpi derive.param2 maxn.
Elpi derive.param2 minn.
Elpi derive.param2 iter.
Elpi derive.param2 iteri.
Elpi derive.param2 iterop.
Elpi derive.param2 Nat.mul.
Elpi derive.param2 muln.
Elpi derive.param2 muln_rec.
Elpi derive.param2 expn.
Elpi derive.param2 expn_rec.
Elpi derive.param2 factorial.
Elpi derive.param2 fact_rec.
Elpi derive.param2 odd.
Elpi derive.param2 double.
Elpi derive.param2 double_rec.

(* Obtained from paramcoq *)
Definition half_R :=
let fix_half_1 : forall _ : nat, nat :=
  fix half (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => uphalf n'
    end
  with uphalf (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => S (half n')
    end
  for
  half in
let fix_half_2 : forall _ : nat, nat :=
  fix half (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => uphalf n'
    end
  with uphalf (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => S (half n')
    end
  for
  half in
let fix_uphalf_1 : forall _ : nat, nat :=
  fix half (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => uphalf n'
    end
  with uphalf (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => S (half n')
    end
  for
  uphalf in
let fix_uphalf_2 : forall _ : nat, nat :=
  fix half (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => uphalf n'
    end
  with uphalf (n : nat) : nat :=
    match n return nat with
    | @O => n
    | @S n' => S (half n')
    end
  for
  uphalf in
fix half_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} : nat_R (fix_half_1 n₁) (fix_half_2 n₂) :=
  let gen_path :
    let half : forall _ : nat, nat :=
      fix half (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half n')
        end
      for
      half in
    let uphalf : forall _ : nat, nat :=
      fix half0 (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half0 n')
        end
      for
      uphalf in
    forall n : nat, @eq nat match n return nat with
                            | @O => n
                            | @S n' => uphalf n'
                            end (half n) :=
    let half : forall _ : nat, nat :=
      fix half (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half n')
        end
      for
      half in
    let uphalf : forall _ : nat, nat :=
      fix half0 (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half0 n')
        end
      for
      uphalf in
    fun n : nat =>
    match n as n0 return (@eq nat match n0 return nat with
                                  | @O => n0
                                  | @S n' => uphalf n'
                                  end (half n0)) with
    | @O => @Logic.eq_refl nat (half O)
    | @S n0 => (fun n1 : nat => @Logic.eq_refl nat (half (S n1))) n0
    end in
  @eq_rect nat match n₁ return nat with
               | @O => n₁
               | @S n' => fix_uphalf_1 n'
               end (fun x : nat => nat_R x (fix_half_2 n₂))
    (@eq_rect nat match n₂ return nat with
                  | @O => n₂
                  | @S n' => fix_uphalf_2 n'
                  end (fun x : nat => nat_R match n₁ return nat with
                                            | @O => n₁
                                            | @S n' => fix_uphalf_1 n'
                                            end x)
       match
         n_R in (nat_R n₁0 n₂0)
         return
           (nat_R match n₁0 return nat with
                  | @O => n₁
                  | @S n' => fix_uphalf_1 n'
                  end match n₂0 return nat with
                      | @O => n₂
                      | @S n' => fix_uphalf_2 n'
                      end)
       with
       | @O_R => n_R
       | @S_R n'₁ n'₂ n'_R => uphalf_R n'₁ n'₂ n'_R
       end (fix_half_2 n₂) (gen_path n₂)) (fix_half_1 n₁) (gen_path n₁)
with uphalf_R (n₁ n₂ : nat) (n_R : nat_R n₁ n₂) {struct n_R} : nat_R (fix_uphalf_1 n₁) (fix_uphalf_2 n₂) :=
  let gen_path :
    let half : forall _ : nat, nat :=
      fix half (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half n')
        end
      for
      half in
    let uphalf : forall _ : nat, nat :=
      fix half0 (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half0 n')
        end
      for
      uphalf in
    forall n : nat, @eq nat match n return nat with
                            | @O => n
                            | @S n' => S (half n')
                            end (uphalf n) :=
    let half : forall _ : nat, nat :=
      fix half (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half n')
        end
      for
      half in
    let uphalf : forall _ : nat, nat :=
      fix half0 (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => uphalf n'
        end
      with uphalf (n : nat) : nat :=
        match n return nat with
        | @O => n
        | @S n' => S (half0 n')
        end
      for
      uphalf in
    fun n : nat =>
    match n as n0 return (@eq nat match n0 return nat with
                                  | @O => n0
                                  | @S n' => S (half n')
                                  end (uphalf n0)) with
    | @O => @Logic.eq_refl nat (uphalf O)
    | @S n0 => (fun n1 : nat => @Logic.eq_refl nat (uphalf (S n1))) n0
    end in
  @eq_rect nat match n₁ return nat with
               | @O => n₁
               | @S n' => S (fix_half_1 n')
               end (fun x : nat => nat_R x (fix_uphalf_2 n₂))
    (@eq_rect nat match n₂ return nat with
                  | @O => n₂
                  | @S n' => S (fix_half_2 n')
                  end (fun x : nat => nat_R match n₁ return nat with
                                            | @O => n₁
                                            | @S n' => S (fix_half_1 n')
                                            end x)
       match
         n_R in (nat_R n₁0 n₂0)
         return
           (nat_R match n₁0 return nat with
                  | @O => n₁
                  | @S n' => S (fix_half_1 n')
                  end match n₂0 return nat with
                      | @O => n₂
                      | @S n' => S (fix_half_2 n')
                      end)
       with
       | @O_R => n_R
       | @S_R n'₁ n'₂ n'_R => @S_R (fix_half_1 n'₁) (fix_half_2 n'₂) (half_R n'₁ n'₂ n'_R)
       end (fix_uphalf_2 n₂) (gen_path n₂)) (fix_uphalf_1 n₁) (gen_path n₁)
for
half_R.
Elpi derive.param2.register half half_R.
(* Elpi derive.param2 half. (* requires mutual inductives *) *)

(** seq *)

(* Here we must make the implicit argument in size explicit *)
Elpi derive.param2 size.

Definition nilp' T (s : seq T) := eqn (size s) 0.
Elpi derive.param2 nilp'.
Definition nilp_R := nilp'_R.
Elpi derive.param2.register nilp nilp_R.

Elpi derive.param2 ohead.
Elpi derive.param2 head.
Elpi derive.param2 behead.
Elpi derive.param2 ncons.
Elpi derive.param2 nseq.
Elpi derive.param2 cat.
Elpi derive.param2 rcons.
Elpi derive.param2 last.
Elpi derive.param2 belast.
Elpi derive.param2 nth.
Elpi derive.param2 set_nth.
Elpi derive.param2 find.
Elpi derive.param2 filter.
Elpi derive.param2 nat_of_bool.
Elpi derive.param2 count.
Elpi derive.param2 has.
Elpi derive.param2 all.
Elpi derive.param2 drop.
Elpi derive.param2 take.
Elpi derive.param2 rot.
Elpi derive.param2 rotr.
Elpi derive.param2 catrev.
Elpi derive.param2 rev.
Elpi derive.param2 map.
Elpi derive.param2 oapp.
Elpi derive.param2 pmap.
Elpi derive.param2 iota.
Elpi derive.param2 mkseq.
Elpi derive.param2 foldr.
Elpi derive.param2 sumn.
Elpi derive.param2 foldl.
Elpi derive.param2 pairmap.
Elpi derive.param2 scanl.
Elpi derive.param2 zip.
Elpi derive.param2 fst.
Elpi derive.param2 snd.
Elpi derive.param2 unzip1.
Elpi derive.param2 unzip2.
Elpi derive.param2 flatten.
Elpi derive.param2 shape.
Elpi derive.param2 reshape.
Elpi derive.param2 allpairs.

(* fintype *)

Elpi derive.param2 predArgType.
Elpi derive.param2 is_true.
Elpi derive.param2 ordinal.
