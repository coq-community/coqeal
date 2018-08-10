Require Import Ncring Ncring_tac.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import div finfun bigop prime binomial ssralg matrix.

Section ring_tac.

Variable R : ringType.

Import GRing.Theory.

Global Instance Rops:
  @Ring_ops R 0%R 1%R (@GRing.add R) (@GRing.mul R)
            (fun a b : R => a - b)%R (@GRing.opp R) eq.

Global Instance R_is_ring: (@Ring _ _ _ _ _ _ _ _ Rops).
constructor=> //.
  exact:eq_equivalence.
  by move=> x y H1 u v H2; rewrite H1 H2.
  by move=> x y H1 u v H2; rewrite H1 H2.
  by move=> x y H1 u v H2; rewrite H1 H2.
  by move=> x y H1; rewrite H1.
  exact:add0r.
  exact:addrC.
  exact:addrA.
  exact:mul1r.
  exact:mulr1.
  exact:mulrA.
  exact:mulrDl.
  by move=> M N P ; exact:mulrDr.
  by move=> M; rewrite /addition /add_notation (addrC M) addNr.
Qed.

Global Instance matrix_ops (R : ringType) (n : nat) : @Ring_ops 'M[R]_n 0%R
  (scalar_mx 1) (@addmx R _ _) mulmx (fun M N => addmx M (oppmx N)) (@oppmx R _ _) eq.

Global Instance matrix_is_ring (R : ringType) (n : nat) :
  (@Ring _ _ _ _ _ _ _ _ (matrix_ops R n)).
Proof.
constructor=> //.
  + exact:eq_equivalence.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1 u v H2; rewrite H1 H2.
  + by move=> x y H1; rewrite H1.
  + exact:add0mx.
  + exact:addmxC.
  + exact:addmxA.
  + exact:mul1mx.
  + exact:mulmx1.
  + exact:mulmxA.
  + exact:mulmxDl.
  + by move=> M N P ; exact:mulmxDr.
  + by move=> M; rewrite /addition /add_notation (addmxC M) addNmx.
Qed.

End ring_tac.