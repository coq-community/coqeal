Add LoadPath "../".

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg poly.
Require Import dvdring cdvdring polydvd Zinfra cseqpoly cseqpolydvd cssralg.

(* Examples of computations over Z[x,y] *)
Module Zxy.
Section Zxy.

Require Import Coq.ZArith.Zdiv Coq.ZArith.Zabs.
Import Zdiv CSeqPoly_dvd CSeqPoly_gcd.

Open Scope Z_scope.

Eval compute in (add 3%Z 4%Z).

Definition p1 : seq Z := [:: 1; 1].
Definition p2 : seq Z := [:: 0; 0; 1].

Eval compute in add p1 p2.

Definition p3 : seq (seq Z) := [:: [::]; [:: 0; 1]; [:: 4%Z; 2%Z]].
Definition p4 : seq (seq Z) := [:: [::]; [::]; [:: 0; 0; 1]].

Eval compute in add p3 p4.
Eval compute in mul p3 p4.

Time Eval compute in cediv 7%Z 2%Z.

Eval compute in odivp_seq p3 p3.
Eval compute in cdiv p3 p3.

(* pxy = (1+x) + (x+x^2)y *)
Definition pxy := [:: [:: 1; 1] ; [:: 0; 1; 1] ].

(* qxy = 1 + (1+x)y + xy^2 *)
Definition qxy := [:: [:: 1]; [:: 1; 1]; [:: 0; 1]].

Time Eval compute in cdiv pxy qxy.
Time Eval compute in gcdp_seq pxy qxy.
Time Eval compute in cgcd pxy qxy.

Definition gcdxy := [:: [:: 1]; [:: 0; 1]].

Time Eval compute in odivp_seq pxy gcdxy.
Time Eval compute in odivp_seq qxy gcdxy.

Time Eval compute in cbezout 2 3.

End Zxy.
End Zxy.

(* Examples of computations over Q[x,y] *)
Module Qxy.
Section Qxy.

Require Import QArith_base Qcanon.
Require Import Qinfra.
Notation "n %:Q" := (n%Z : Qcb) (at level 2, left associativity, format "n %:Q").

Import CSeqPoly_dvd CSeqPoly_gcd.

Time Eval vm_compute in add_seq [:: (-2)%:Q; 3%:Q] [:: 1%:Q; 2%:Q; 3%:Q].
Time Eval vm_compute in mul_seq [:: (-2)%:Q; 3%:Q] [:: 1%:Q; 2%:Q; 3%:Q].
Time Eval compute in cbezout 2%:Q 3%:Q.

Time Eval vm_compute in gcdp_seq [:: (-2)%:Q; 3%:Q] [:: 1%:Q; 2%:Q; 3%:Q].

Time Eval vm_compute in
  gcdp_seq [:: 14%:Q; (-3)%:Q; 4%:Q; (-4)%:Q; 1%:Q ]
          [:: 6%:Q; 17%:Q; 12%:Q; 8%:Q; 1%:Q].
Time Eval vm_compute in
  gcdp_seq [:: (-5)%:Q; 2%:Q; 8%:Q; (-3)%:Q; (-3)%:Q; 0%:Q; 1%:Q; 0%:Q; 1%:Q ]
          [:: 21%:Q; (-9)%:Q; (-4)%:Q; 0%:Q; 5%:Q; 0%:Q; 3%:Q].

(* pxy = (1+x) + (x+x^2)y *)
Definition pxyQ := [:: [:: 1%:Q; 1%:Q] ; [:: 0%:Q; 1%:Q; 1%:Q] ].

(* qxy = 1 + (1+x)y + xy^2 *)
Definition qxyQ := [:: [:: 1%:Q]; [:: 1%:Q; 1%:Q]; [:: 0%:Q; 1%:Q]].

Time Eval compute in cdiv pxyQ qxyQ.
Time Eval compute in gcdp_seq pxyQ qxyQ.

Open Scope Q_scope.

Definition px := [::(-5)%:Q;2%:Q;8%:Q;(-3)%:Q;(-3)%:Q;0%:Q;1%:Q;0%:Q;1%:Q].
Definition qx := [::21%:Q;(-9)%:Q;(-4)%:Q;0%:Q;5%:Q;0%:Q;3%:Q].

Time Eval compute in gcdp_seq px qx.

Time Eval compute in
  gcdp_seq [:: (-5); 2; 8; (-3); (-3); 0%:Q; 1%:Q; 0%:Q; 1%:Q ]
           [:: 21%:Q; (-9)%:Q; (-4)%:Q; 0%:Q; 5%:Q; 0%:Q; 3%:Q].


End Qxy.
End Qxy.

(* Examples of computations over Q[x] *)
Module Qx.
Section Qx.

Require Import Qinfra QArith_base Qcanon.
Import KX.

Notation "n %:Q" := (n%Z : Qcb) (at level 2, left associativity, format "n %:Q").

Time Eval vm_compute in cediv [::] [:: 1%:Q].
Time Eval vm_compute in cediv [:: 1%:Q] [::].
Time Eval vm_compute in ediv_seq [::] [:: 1%:Q].
Time Eval vm_compute in ediv_seq [:: 1%:Q] [::].
Time Eval vm_compute in egcd_seq [:: 2%:Q; 3%:Q] [:: 2%:Q; 3%:Q].
Time Eval vm_compute in gcd_seq [:: 1%:Q] [::].
Time Eval vm_compute in
  gcd_seq [:: 14%:Q; (-3)%:Q; 4%:Q; (-4)%:Q; 1%:Q ]
          [:: 6%:Q; 17%:Q; 12%:Q; 8%:Q; 1%:Q].
Time Eval vm_compute in
  gcd_seq [:: (-5)%:Q; 2%:Q; 8%:Q; (-3)%:Q; (-3)%:Q; 0%:Q; 1%:Q; 0%:Q; 1%:Q ]
          [:: 21%:Q; (-9)%:Q; (-4)%:Q; 0%:Q; 5%:Q; 0%:Q; 3%:Q].

End Qx.
End Qx.