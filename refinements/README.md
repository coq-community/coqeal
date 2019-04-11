CoqEAL - Refinements Package
============================

Content
-------

- `refinements`: Classes for refinements and refines together with
  operational typeclasses for common operations.

- `binnat`: Proof that the binary naturals of Coq (`N`) is a refinement
  of SSReflect unary naturals (`nat`) together with basic operations.

- `binint`: SSReflect integers (`ssrint`) are refined to a new type
  paremetrized by positive numbers (represented by a sigma type) and
  natural numbers.  This means that proofs can be done using only
  lemmas from the SSReflect library which leads to simpler proofs than
  previous versions of `binint`.  (e.g. `N`).

- `rational`: The rational numbers of SSReflect (`rat`) is refined to
  pairs of elements refining integers using parametricity of
  refinements.

- `seqmatrix`: First and incomplete attempt to refine SSReflect
  matrices `M[R]_(m,n)`) to lists of lists (`seq (seq R)`).
  (work in progress).

- `seqpoly`: First and incomplete attempt to refine SSReflect
  polynomials (`{poly R}`) to lists (`seq R`). (work in progress).

- [...]

Conventions
-----------

- Files should follow this pattern (wrt `Local` and `Global` instances):

```coq
(** Part 1: Generic operations *)
Section generic_operations.

Global Instance generic_operation := ...

(** Part 2: Correctness proof for proof-oriented types and programs *)
Section theory.

Local Instance param_correctness : param ...

(** Part 3: Parametricity *)
Section parametricity.

Global Instance param_parametricit : param ...
Proof. exact: param_trans. Qed.

End parametricity.
End theory.
```
