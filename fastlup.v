Require Import Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp matrix mxalgebra refinements mxstructure seqmatrix strassen.

Section prelude.

Import GRing.Theory.

Variable F : fieldType.

Local Open Scope ring_scope.

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

End prelude.

Section fast_triangular.

Variable F : fieldType.

Local Coercion nat_of_pos : positive >-> nat.

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

Local Open Scope ring_scope.

(* xI p case is wrong for now *)
Fixpoint upper_tri_inv {n : positive} :=
  match n return let M := 'M[F]_n in M -> M with
  | xH => fun A => (A 0 0)^-1%:M
  | xO p => fun A => let A := castmx (addpp _, addpp _) A in
            let iA1 := upper_tri_inv (ulsubmx A) in
            let iA3 := upper_tri_inv (drsubmx A) in
            let R := Strassen _ (Strassen _ (- iA1) (ursubmx A)) iA3 in
            castmx (esym (addpp _), esym (addpp _)) (block_mx iA1 R 0 iA3)
  | xI p => fun A => let A := castmx (addpp1 _, addpp1 _) A in
            let iA1 := upper_tri_inv (ulsubmx A) in
            let A2 := ursubmx A in
            let lA2 := lsubmx A2 in
            let rA2 := rsubmx A2 in
            let A3 := drsubmx A in
            let A3ul := ulsubmx A3 in
            let A3ur := ursubmx A3 in
            let A3dr := drsubmx A3 in
            let iA3ul := upper_tri_inv A3ul in
            let iA3dr := (A3dr 0 0)^-1%:M in (* Could be improved *)
            let R3 := - iA3ul *m A3ur *m iA3dr in
            let iA3 := block_mx iA3ul R3 0 iA3dr in
            let R := row_mx (- iA1 *m lA2 *m iA3ul)
              (Strassen _ (Strassen _ iA1 lA2) iA3ul *m A3ur *m iA3dr +
              - iA1 *m rA2 *m iA3dr)
            in
            castmx (esym (addpp1 _), esym (addpp1 _)) (block_mx iA1 R 0 iA3)
  end.

(*
Fixpoint upper_tri_inv {n : positive} :=
  match n return let M := 'M[F]_n in M -> M with
  | xH => fun A => (A 0 0)^-1%:M
  | xO p => fun A => let A := castmx (addpp _, addpp _) A in
            let iA1 := tri_inv (ulsubmx A) in
            let iA2 := tri_inv (drsubmx A) in
            let R := - Strassen _ (Strassen _ iA2 (dlsubmx A)) iA1 in
            castmx (esym (addpp _), esym (addpp _)) (block_mx iA1 0 R iA2)
  | xI p => fun A => let A := castmx (addpp1 _, addpp1 _) A in
            let iA1 := tri_inv (ulsubmx A) in
            let A2 := drsubmx A in
            let dlA2 := dlsubmx A2 in
            let drA2 := drsubmx A2 in
            let ulA2 := ulsubmx A2 in
            let iulA2 := tri_inv ulA2 in
            let R' := - drA2 *m dlA2 *m iulA2 in
            let iA2 := block_mx iulA2 0 R' (drA2 0 0)^-1%:M in
            let A3 := dlsubmx A in
            let uA3 := usubmx A3 in let dA3 := dsubmx A3 in
            let uR := Strassen _ (Strassen _ ulA2 uA3) iA1 in
            let dR := (dlA2 *m uA3 + drA2 *m dA3) *m iA1 in
            castmx (esym (addpp1 _), esym (addpp1 _)) (block_mx iA1 0 (- col_mx uR dR) iA2)
  end.
*)

Lemma tri_invP (p : positive) (M : 'M[F]_p) :
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
  rewrite -{1}[castmx _ _]submxK Mdl0 invmx_ublock // !IHp // !StrassenP.
  rewrite -{1 2}[drsubmx _]submxK Mdrdl0 invmx_ublock //.
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
  rewrite /= !IHp // !StrassenP; apply/esym/castmx_sym.
  by rewrite -invmx_ublock // -Mdl0 submxK; case: _ / (addpp p).
by rewrite {2}[M]mx11_scalar invmx_scalar.
Qed.

End fast_triangular.

Section Bunch_Hopcroft.

Variable F : fieldType.

Local Coercion nat_of_pos : positive >-> nat.

Variable f : forall n, 'rV[F]_n -> option 'I_n.

Fixpoint lup (m n : positive) :=
  match m return 'M[F]_(m,n) -> 'M[F]_m * 'M[F]_(m,n) * 'M[F]_n with
  | xH => fun A => let A := castmx (erefl _, esym (predpK _)) A in
    if f _ A is Some i then
      let U := castmx (erefl _, predpK _) (xcol 0%R i A) in
      let P := castmx (predpK _, predpK _) (tperm_mx 0%R i) in
      (1, U, P)%R
    else (0,0,0)%R
  | xO p => fun A => 
    let A := castmx (addpp p,erefl _) A in (0,0,0)%R
  | xI p => fun _ => (0,0,0)%R
  end.

End Bunch_Hopcroft.
