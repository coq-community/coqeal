Add LoadPath "../".

Require Import seq cseqpoly cssralg Zinfra karatsuba ssrnat.
Require Import ZArith.

Open Scope Z_scope.


(* Degree 10 polynomial *)
Definition p10 := map Z_of_nat (iota 1 10).

Time Eval vm_compute in size (mul_seq p10 p10).
Time Eval vm_compute in size (karatsuba_seq p10 p10).


(* Degree 50 *)
Definition p50 := map Z_of_nat (iota 1 50).

Time Eval vm_compute in size (mul_seq p50 p50).
Time Eval vm_compute in size (karatsuba_seq p50 p50).


(* Degree 100 *)
Definition p100 := map Z_of_nat (iota 1 100).

Time Eval vm_compute in size (mul_seq p100 p100).
Time Eval vm_compute in size (karatsuba_seq p100 p100).

(* Degree 200 *)
Definition p200 := map Z_of_nat (iota 1 200).

Time Eval vm_compute in size (mul_seq p200 p200).
Time Eval vm_compute in size (karatsuba_seq p200 p200).


(* Degree 300 *)
Definition p300 := map Z_of_nat (iota 1 300).

Time Eval vm_compute in size (mul_seq p300 p300).
Time Eval vm_compute in size (karatsuba_seq p300 p300).


(* Degree 400 *)
Definition p400 := map Z_of_nat (iota 1 400).

Time Eval vm_compute in size (mul_seq p400 p400).
Time Eval vm_compute in size (karatsuba_seq p400 p400).


(* Degree 500 *)
Definition p500 := map Z_of_nat (iota 1 500).

Time Eval vm_compute in size (mul_seq p500 p500).
Time Eval vm_compute in size (karatsuba_seq p500 p500).


(* Degree 600 *)
Definition p600 := map Z_of_nat (iota 1 600).

Time Eval vm_compute in size (mul_seq p600 p600).
Time Eval vm_compute in size (karatsuba_seq p600 p600).


(* Degree 700 *)
Definition p700 := map Z_of_nat (iota 1 700).

Time Eval vm_compute in size (mul_seq p700 p700).
Time Eval vm_compute in size (karatsuba_seq p700 p700).


(* Degree 800 *)
Definition p800 := map Z_of_nat (iota 1 800).

Time Eval vm_compute in size (mul_seq p800 p800).
Time Eval vm_compute in size (karatsuba_seq p800 p800).


(* Degree 900 *)
Definition p900 := map Z_of_nat (iota 1 900).

Time Eval vm_compute in size (mul_seq p900 p900).
Time Eval vm_compute in size (karatsuba_seq p900 p900).


(* Degree 1000 *)
Definition p1000 := map Z_of_nat (iota 1 1000).

Time Eval vm_compute in size (mul_seq p1000 p1000).
Time Eval vm_compute in size (karatsuba_seq p1000 p1000).







(* Genreate tons of test computations to check that karatsuba is fast by
Prelude> let f x = "Definition p" ++ x ++ " := map Z_of_nat (iota 1 " ++ x ++ ").\nTime Eval compute in karatsuba_seq p" ++ x ++" p" ++ x ++ ".\n"
Prelude> writeFile "temp.v" (unlines [ (f (show x)) | x <- [1..500]])
*)