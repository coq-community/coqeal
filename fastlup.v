Require Import Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix mxalgebra refinements mxstructure seqmatrix strassen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section prelude.

Import GRing.Theory.

Variable F : fieldType.

Local Open Scope ring_scope.

Lemma mulmx_cast {R' : ringType} {m n p m' n' p'} {M:'M[R']_(m,p)} {N:'M_(p,n)}
  {eqm : m = m'} (eqp : p = p') {eqn : n = n'} :
  castmx (eqm,eqn) (M *m N) = castmx (eqm,eqp) M *m castmx (eqp,eqn) N.
Proof. by case eqm ; case eqn ; case eqp. Qed.

Lemma invmx_ublock m n (Aul : 'M[F]_m) Aur (Adr : 'M[F]_n) :
  block_mx Aul Aur 0 Adr \in unitmx ->
  invmx (block_mx Aul Aur 0 Adr) = block_mx (invmx Aul) (- invmx Aul *m Aur *m invmx Adr) 0 (invmx Adr).
Proof.
move=> unitA.
move: (unitA); rewrite -row_full_unit => fullA.
move: (unitA); rewrite unitmxE det_ublock unitrM.
case/andP; rewrite -!unitmxE => unitAul unitAdr.
apply: (row_full_inj fullA).
rewrite mulmxV //.
rewrite mulmx_block.
rewrite !mul0mx !mulmx0 !add0r addr0.
rewrite !mulmxA mulmxN.
rewrite !mulmxV //.
rewrite !mulNmx mul1mx addNr.
by rewrite -scalar_mx_block.
Qed.

(*
Lemma invmx_ublock m n (Aul : 'M[R]_m.+1) Aur (Adr : 'M[R]_n.+1) :
  block_mx Aul Aur 0 Adr \is a GRing.unit ->
  (block_mx Aul Aur 0 Adr)^-1 = block_mx Aul^-1 (- Aul^-1 *m Aur *m Adr^-1) 0 Adr^-1.
Proof.
move=> unitA.
apply (mulrI unitA).
move: (unitA).
rewrite unitmxE det_ublock unitrM.
case/andP => unitAul unitAdr.
rewrite divrr //.
rewrite -mulmxE.
(* Why do we have to specify arguments here? *)
rewrite (mulmx_block Aul Aur 0 Adr Aul^-1).
rewrite !mul0mx !mulmx0 !add0r addr0.
rewrite !mulmxA mulmxN !mulmxE !divrr //.
rewrite !mulNmx mul1mx addNr.
by rewrite -scalar_mx_block.
Qed.

Lemma invmx_lblock m n (Aul : 'M[R]_m.+1) Adl (Adr : 'M[R]_n.+1) :
  block_mx Aul 0 Adl Adr \is a GRing.unit ->
  (block_mx Aul 0 Adl Adr)^-1 = block_mx Aul^-1 0 (- Adr^-1 *m Adl *m Aul^-1) Adr^-1.
Proof.
move=> unitA.
apply (mulrI unitA).
move: (unitA).
rewrite unitmxE det_lblock unitrM.
case/andP => unitAul unitAdr.
rewrite divrr //.
rewrite -mulmxE.
(* Why do we have to specify arguments here? *)
rewrite (mulmx_block Aul 0 Adl Adr Aul^-1 0 _ Adr^-1).
rewrite !mul0mx !mulmx0 !add0r addr0.
rewrite !mulmxA mulmxN !mulmxE !divrr //.
rewrite !mulNmx mul1mx subrr.
by rewrite -scalar_mx_block.
Qed.

*)

Definition perm_union_fun {m n} (s1 : 'S_m) (s2 : 'S_n) jk :=
  match (split jk) with
  | inl j => lshift _ (s1 j)
  | inr k => rshift _ (s2 k)
  end.

Lemma ltn_lshift {m} n i : @lshift m n i < m.
Proof. exact: ltn_ord. Qed.

Lemma ltn_rshift m n i : m <= @rshift m n i.
Proof. exact: leq_addr. Qed.

Lemma perm_unionK m n s1 s2 :
  cancel (@perm_union_fun m n s1 s2) (@perm_union_fun m n (s1^-1) (s2^-1)).
Proof.
move=> jk; rewrite /perm_union_fun.
case: (splitP jk) => [j|k] eq_jk.
have := ltn_lshift n (s1 j).
case: splitP => //= j' /val_inj <- _.
  by rewrite permK; apply: val_inj.
have := ltn_rshift m (s2 k).
rewrite leqNgt; case: splitP => //= k' /addnI /val_inj <- _; rewrite permK.
by apply: val_inj.
Qed.

Lemma perm_union_subproof m n (s1 : 'S_m) (s2 : 'S_n) :
  injective (perm_union_fun s1 s2).
Proof. exact: (can_inj (perm_unionK s1 s2)). Qed.

Definition perm_union m n s1 s2 : 'S_(m + n) :=
  perm (@perm_union_subproof m n s1 s2).

Definition cast_perm_fun m n (eq_mn : m = n) (s : 'S_m) k :=
  cast_ord eq_mn (s (cast_ord (esym eq_mn) k)).

Lemma cast_perm_subproof m n eq_mn s : injective (@cast_perm_fun m n eq_mn s).
Proof.
move: s; case: _ / eq_mn => s k l /=.
rewrite /cast_perm_fun /= !cast_ord_id.
exact: perm_inj.
Qed.

Definition cast_perm m n eq_mn s :=
  perm (@cast_perm_subproof m n eq_mn s).

End prelude.

Section fast_triangular.

Local Coercion nat_of_pos : positive >-> nat.

Section fast_triangular_generic.

Lemma addpp p : xO p = (p + p)%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addSpp p : xI p = (p + p).+1%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnn. Qed.

Lemma addp1 p : xI p = (xO p + 1)%N :> nat.
Proof. by rewrite addn1. Qed.

Lemma addpp1 p : xI p = (p + (p + 1))%N :> nat.
Proof. by rewrite /= NatTrec.trecE addnA addnn addn1. Qed.

Lemma lt0p : forall p : positive, 0 < p.
Proof.
by elim=> // p IHp /=; rewrite NatTrec.doubleE -addnn; exact:ltn_addl.
Qed.

Lemma predpK (p : positive) : p.-1.+1 = p.
Proof. exact/prednK/lt0p. Qed.

Local Open Scope computable_scope.
Local Open Scope hetero_computable_scope.

Import Refinements.Op.

Variable A : Type.
Variable ordA : nat -> Type.
Variable mxA : nat -> nat -> Type.

Context `{forall n, zero (ordA n.+1)}.
Context `{inv A}.
Context `{!hzero mxA, !hone mxA, !hadd mxA, !hopp mxA, !hsub mxA, !hmul mxA}.
Context `{!ulsub mxA, !ursub mxA, !dlsub mxA, !drsub mxA, !block mxA}.
Context `{!lsub mxA, !rsub mxA, !row mxA}.
Context `{!fun_of A ordA mxA, !scalar A mxA, !hcast mxA}.

Typeclasses eauto := debug.

(* The type annotation in the last branch is required to prevent typechecking *)
(* from diverging... *)
Fixpoint upper_tri_inv {n : positive} : mxA n n -> mxA n n :=
  match n return let M := mxA n n in M -> M with
  | xH => fun A => (fun_of_matrix A 0%C 0%C)^-1%:M
  | xO p => fun A => let A := castmx (addpp p, addpp p) A in
            let iA1 := @upper_tri_inv p (ulsubmx A) in
            let iA3 := @upper_tri_inv p (drsubmx A) in
            let R := Strassen (Strassen (- iA1) (ursubmx A)) iA3 in
            castmx (esym (addpp p), esym (addpp p)) (block_mx iA1 R 0 iA3)
  | xI p => fun (A' : mxA (xI p) (xI p)) => let A := castmx (addpp1 p, addpp1 p) A' in
            let iA1 := @upper_tri_inv p (ulsubmx A) in
            let A2 := ursubmx A in
            let lA2 := lsubmx A2 in
            let rA2 := rsubmx A2 in
            let A3 := drsubmx A in
            let A3ul := ulsubmx A3 in
            let A3ur := ursubmx A3 in
            let A3dr := drsubmx A3 in
            let iA3ul := @upper_tri_inv p A3ul in
            let iA3dr := (fun_of_matrix A3dr 0%C 0%C)^-1%:M in (* Could be improved *)
            let R3 := - iA3ul *m A3ur *m iA3dr in
            let iA3 := block_mx iA3ul R3 0 iA3dr in
            let R := row_mx (- iA1 *m lA2 *m iA3ul)
              (Strassen (Strassen iA1 lA2) iA3ul *m A3ur *m iA3dr +
              - iA1 *m rA2 *m iA3dr)
            in
            castmx (esym (addpp1 p), esym (addpp1 p)) (block_mx iA1 R (0 : mxA (p + 1) p) iA3)
  end.

End fast_triangular_generic.

Section fast_triangular_correctness.

Variable F : fieldType.

Instance : Refinements.Op.inv F := GRing.inv.
Instance zero_ordinal n : Refinements.Op.zero (@ordinal n.+1) := 0%R.
Instance zero_mx : Refinements.Op.hzero (matrix F) := fun m n => 0%R.
Instance : Refinements.Op.hadd (matrix F) := @addmx F.
Instance : Refinements.Op.hopp (matrix F) := @oppmx F.
Instance : Refinements.Op.hsub (matrix F) := (fun _ _ M N => addmx M (oppmx N)).
Instance : Refinements.Op.hmul (matrix F) := @mulmx F.
Instance : Refinements.Op.hcast (matrix F) := @matrix.castmx F.
Instance : Refinements.Op.ulsub (matrix F) := @matrix.ulsubmx F.
Instance : Refinements.Op.ursub (matrix F) := @matrix.ursubmx F.
Instance : Refinements.Op.dlsub (matrix F) := @matrix.dlsubmx F.
Instance : Refinements.Op.drsub (matrix F) := @matrix.drsubmx F.
Instance : Refinements.Op.block (matrix F) := @matrix.block_mx F.
Instance : Refinements.Op.lsub (matrix F) := @matrix.lsubmx F.
Instance : Refinements.Op.rsub (matrix F) := @matrix.rsubmx F.
Instance : Refinements.Op.row (matrix F) := @matrix.row_mx F.
Instance : Refinements.Op.scalar F (matrix F) := @matrix.scalar_mx F.
Instance : Refinements.Op.fun_of F (@ordinal) (matrix F) := (@matrix.fun_of_matrix F).

Ltac simpC2 :=
  do ?[ rewrite -[0%C]/0%R | rewrite -[1%C]/1%R
      | rewrite -[(_ + _)%C]/(_ + _)%R
      | rewrite -[(_ + _)%C]/(_ + _)%N
      | rewrite -[(- _)%C]/(- _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%R
      | rewrite -[(_ - _)%C]/(_ - _)%N
      | rewrite -[(_ * _)%C]/(_ * _)%R
      | rewrite -[(_ * _)%C]/(_ * _)%N
      | rewrite -[_^-1%C]/(_^-1%R)
      | rewrite -[(_ *: _)%C]/(_ *: _)%R
      | rewrite -[(_ / _)%C]/(_ / _)%R
      | rewrite -[(_ == _)%C]/(_ == _)%bool
      | rewrite -[(_ <= _)%C]/(_ <= _)%R
      | rewrite -[(_ < _)%C]/(_ < _)%R
      | rewrite -[(_ <= _)%C]/(_ <= _)%N
      | rewrite -[(_ < _)%C]/(_ < _)%N
      | rewrite -[0%HC]/(const_mx 0)
      | rewrite -[1%HC]/1%R
(* Missing in simpC *) | rewrite -[_%:M%HC]/(_%:M%R)
(* To be removed *) | rewrite -[_%:M%C]/(_%:M%R)
      | rewrite -[(- _)%HC]/(- _)%R
      | rewrite -[(_ + _)%HC]/(_ + _)%R
      | rewrite -[(_ - _)%HC]/(_ - _)%R
      | rewrite -[Refinements.Op.hsub_op _ _]/(fun _ _ => addmx _ (oppmx _))
      | rewrite -[Refinements.Op.heq_op _ _]/(_ == _)%bool
      | rewrite -[(_ *m _)%HC]/(_ *m _)%R
(* To be removed *)      | rewrite -[Refinements.Op.hmul_op _ _]/(mulmx _ _)
(* To be removed *)      | rewrite -[Refinements.Op.hadd_op _ _]/(addmx _ _)
(* To be removed *)      | rewrite -[Refinements.Op.hopp_op _]/(oppmx _)
      | rewrite -[Refinements.Op.invmx _]/(invmx _)
      | rewrite -[Refinements.Op.castmx _ _]/(castmx _ _)
      | rewrite -[Refinements.Op.usubmx _]/(usubmx _)
      | rewrite -[Refinements.Op.dsubmx _]/(dsubmx _)
      | rewrite -[Refinements.Op.lsubmx _]/(lsubmx _)
      | rewrite -[Refinements.Op.rsubmx _]/(rsubmx _)
      | rewrite -[Refinements.Op.ulsubmx _]/(ulsubmx _)
      | rewrite -[Refinements.Op.ursubmx _]/(ursubmx _)
      | rewrite -[Refinements.Op.dlsubmx _]/(dlsubmx _)
      | rewrite -[Refinements.Op.drsubmx _]/(drsubmx _)
      | rewrite -[Refinements.Op.row_mx _ _]/(row_mx _ _)
      | rewrite -[Refinements.Op.col_mx _ _]/(col_mx _ _)
      | rewrite -[Refinements.Op.block_mx _ _ _ _]/(block_mx _ _ _ _)
      | rewrite -[Refinements.Op.fun_of_matrix _]/(fun_of_matrix _)].

Lemma upper_tri_invP (p : positive) (M : 'M[F]_p) :
  M \in unitmx -> upper_triangular_mx M -> upper_tri_inv M = invmx M.
Proof.
elim: p M => [p IHp|p IHp|] M unitM triM.
+ have {unitM}unitM: castmx (addpp1 p, addpp1 p) M \in unitmx.
    by move: M unitM triM; case: _ / (addpp1 p).
  have {triM}triM: upper_triangular_mx (castmx (addpp1 p, addpp1 p) M).
    by move: M unitM triM; case: _ / (addpp1 p).
  rewrite -[castmx _ _]submxK in triM unitM.
  have Mdl0 := (upper_triangular_block_mxdl triM (leqnn _)).
  move: (unitM); rewrite Mdl0 in triM unitM *.
  rewrite unitmxE det_ublock GRing.unitrM; case/andP => unitMul unitMdr.
  have triMdr := (upper_triangular_block_mxdr triM (leqnn _)).
  have triMul := (upper_triangular_block_mxul triM).
  rewrite -[drsubmx _]submxK in triMdr unitMdr.
  have Mdrdl0 := (upper_triangular_block_mxdl triMdr (leqnn _)).
  move: (unitMdr); rewrite Mdrdl0 in triMdr unitMdr *.
  rewrite det_ublock GRing.unitrM; case/andP => unitMdrul unitMdrdr.
  have triMdrdr := (upper_triangular_block_mxdr triMdr (leqnn _)).
  have triMdrul := (upper_triangular_block_mxul triMdr).
  rewrite /=; apply/esym/castmx_sym/esym.
  have->: castmx (addpp1 p, addpp1 p) (invmx M) = invmx (castmx (addpp1 p, addpp1 p) M).
    by case: _ / (addpp1 p).
(* TODO revert -!StrassenP to !StrassenP *)
  rewrite -{1}[castmx _ _]submxK Mdl0 invmx_ublock // !IHp // -!StrassenP.
  rewrite -{1 2}[drsubmx _]submxK Mdrdl0 invmx_ublock //.
simpC2.
  rewrite -invmx_scalar -mx11_scalar.
  congr block_mx.
  rewrite -{1}[ursubmx _]hsubmxK mul_mx_row mul_row_block.
  congr row_mx; first by rewrite !mulmx0 GRing.addr0.
  by rewrite !mulNmx mulmxN GRing.opprK !mulmxA.
+ have {triM}triM: upper_triangular_mx (castmx (addpp p, addpp p) M).
    by move: M unitM triM; case: _ / (addpp p).
  have {unitM}unitM: castmx (addpp p, addpp p) M \in unitmx.
    by move: M unitM triM; case: _ / (addpp p).
  rewrite -[castmx _ _]submxK in triM unitM.
  have Mdl0 := (upper_triangular_block_mxdl triM (leqnn _)).
  move: (unitM); rewrite Mdl0 in triM unitM *.
  rewrite unitmxE det_ublock GRing.unitrM; case/andP => unitMul unitMdr.
  have triMdr := (upper_triangular_block_mxdr triM (leqnn _)).
  have triMul := (upper_triangular_block_mxul triM).
  rewrite /= !IHp // -!StrassenP; apply/esym/castmx_sym.
  by simpC2; rewrite -invmx_ublock // -Mdl0 submxK; case: _ / (addpp p).
by rewrite {2}[M]mx11_scalar invmx_scalar.
Qed.

End fast_triangular_correctness.

End fast_triangular.

Section Bunch_Hopcroft.

Local Open Scope nat_scope.

Lemma foo {n p} : p <= n -> p + (n - p).+1 = n.+1.
Proof.
by move=> le_pn; rewrite -subSn // subnKC //; apply: ltnW.
Qed.

Variable F : fieldType.

Local Coercion nat_of_pos : positive >-> nat.

Local Open Scope ring_scope.

Variable f : forall n, 'rV[F]_n -> option 'I_n.

Fixpoint lup {m : positive} {n : nat} :=
  match m return 'M[F]_(m,n.+1) -> option ('M[F]_m * 'M[F]_(m,n.+1) * 'S_n.+1) with
  | xH => fun A =>
    if f A is Some i then
      let U := xcol 0%R i A in
      let P := tperm 0%R i in
      Some (1, U, P)%R
    else None
  | xO p => fun A => 
    let A := castmx (addpp p, erefl _) A in
    if lup (usubmx A) is Some (L1, U1, P1) then
      let B2 := col_perm P1 (dsubmx A) in (* P1^-1 ? *)
      if @idP (p <= n) is ReflectT lt_mn then
        let U1 := castmx (erefl _, esym (subnKC (leqW lt_mn))) U1 in
        let V1 := lsubmx U1 in let B := rsubmx U1 in
        let V2 := upper_tri_inv V1 in
        let B2 := castmx (erefl _, esym (subnKC (leqW lt_mn))) B2 in
        let C := lsubmx B2 in let D := rsubmx B2 in
        let C1 := Strassen C V2 in
        let F := C1 *m B in (* Should it be Strassen here? *)
        let E := castmx (erefl _, subSn lt_mn) (D - F) in
        if lup E is Some (L2, U2, P2) then
          let B2 := col_perm P2 (castmx (erefl _, subSn lt_mn) B) in (* P2^-1 ?*)
          let P := (P1 * cast_perm (foo lt_mn) (@perm_union p _ 1 P2))%g in
          let L := castmx (esym (addpp _), esym (addpp _)) (block_mx L1 0 C1 L2) in
          let U := castmx (esym (addpp _), foo lt_mn) (block_mx V1 B2 0 U2) in
          Some (L,U,P)%R
        else None
      else None
    else None 
  | xI p => fun _ => Some (0,0,1%g)%R
  end.

End Bunch_Hopcroft.

Section Bunch_Hopcroft_correctness.

Variable F : fieldType.

Local Coercion nat_of_pos : positive >-> nat.

Local Open Scope ring_scope.

CoInductive lup_spec (m : positive) n (M : 'M[F]_(m,n.+1)) :
  option ('M[F]_m * 'M[F]_(m,n.+1) * 'S_n.+1) -> Type :=
  | LupSpec L U P of col_perm P M = L *m U
      & lower_triangular_mx L 
      & upper_triangular_mx U
      & (forall i, L i i = 1)
      & \rank U = m :
      (* Fortement régulière ?
      & (forall (i : 'I_m) (j : 'I_n.+1), i == j :> nat -> U i j \is a GRing.unit) :
      *)

      lup_spec M (Some (L,U,P)).

      (*
  | LupDegenerate of \rank M < m : lup_spec M None.
*)

Lemma lupP (m : positive) n f (M : 'M[F]_(m,n.+1)) :
  (forall k (A : 'rV_k), pick_spec [pred i | A 0 i != 0] (f _ A)) ->
  \rank M = m -> lup_spec M (lup f M).
Proof.
elim: m n M => [p IHp|p IHp|] n M pickf rk_M /=.
+ admit.
+ case: IHp => // [|L1 U1 P1 corrM1 triL1 triU1 diagL1 rk_u1].
    move: rk_M.
    have->: \rank M = \rank (castmx (addpp p, erefl n.+1) M).
      by case: _ / (addpp p).
    rewrite -{1}[castmx _ _]vsubmxK.
    rewrite -addsmxE.
    admit.
  case (@idP (p <= n)) => [le_pn|lt_np]; last first.
  suff: False => //.
  move/negP: lt_np.
rewrite -ltnNge.
rewrite rank_leq_col.

case: pickf => [i /= nz_m0i0|eq_M0].
  constructor.
  - by rewrite xcolE col_permE tpermV mul1mx.
  - admit.
  - admit.
  - by move=> k; rewrite mxE eqxx.
  by rewrite xcolE mxrankMfree // row_free_unit unitmx_perm.
admit.

rewrite ltnS leqn0 mxrank_eq0.
apply/eqP/matrixP => i j.
by rewrite ord1 mxE; have := (eq_M0 j) => /= /negbFE /eqP.




Lemma lupP (m : positive) n f (M : 'M[F]_(m,n.+1)) :
  (forall k (A : 'rV_k), pick_spec [pred i | A 0 i != 0] (f _ A)) ->
      lup_spec M (lup f M).
Proof.
elim: m n M => [p IHp|p IHp|] n M pickf /=.
+ admit.
+ case: (IHp _ _ pickf) => [L1 U1 P1 corrM1|rk_Mu].
  (* Coq's case seems more powerful here, probably because SSR picks *
   * all occurrences of b1 in idP : reflect b1 b1                    *)
    case (@idP (p <= n)) => [le_pn|lt_np].
      rewrite StrassenP.
      case: (IHp _ _ pickf) => [L2 U2 P2 corrE|rk_E]; constructor.
rewrite -mulmx_cast.
rewrite upper_tri_invP.
set U1' := castmx _ U1.
set M' := castmx _ M.


rewrite mulmx_block.
rewrite !mul0mx !mulmx0 !GRing.addr0.
rewrite -[_ *m invmx _ *m _]mulmxA.
rewrite mulVmx.
rewrite mulmx1.


      admit.
    constructor.
    move/negP: lt_np; rewrite -ltnNge {2}addpp => lt_np.
    apply: (leq_ltn_trans (rank_leq_col _)).
    rewrite -addn1.
    apply: leq_add => //.
    exact: lt0p.
  constructor.
  have->: \rank M = \rank (castmx (addpp p, erefl n.+1) M).
    by case: _ / (addpp p).
  rewrite -[castmx _ _]vsubmxK.
  rewrite -addsmxE.
  apply: (leq_ltn_trans (mxrank_adds_leqif _ _)).
  rewrite {5}addpp.
  rewrite -addSn.
  apply: leq_add => //.
  exact: rank_leq_row.
case: pickf => [i /= nz_m0i0|eq_M0]; constructor.
  by rewrite xcolE col_permE tpermV mul1mx.
rewrite ltnS leqn0 mxrank_eq0.
apply/eqP/matrixP => i j.
by rewrite ord1 mxE; have := (eq_M0 j) => /= /negbFE /eqP.
Qed.

End Bunch_Hopcroft_correctness.
