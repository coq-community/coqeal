Require Import Ncring Ncring_tac.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg.

Section ring_tac.

Variable R : ringType.

Import GRing.Theory.

Global Instance Rops:@Ring_ops R 0%R 1%R (@GRing.add R) (@GRing.mul R) (fun a b : R => a - b)%R (@GRing.opp R) eq.

Global Instance Zr: (@Ring _ _ _ _ _ _ _ _ Rops).
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
  exact:mulr_addl.
  by move=> M N P ; exact:mulr_addr.
  by move=> M; rewrite /addition /add_notation (addrC M) addNr.
Qed.

End ring_tac.

Goal (forall R : ringType, forall a b : R, a + b = b + a)%R.
by non_commutative_ring.
Qed.