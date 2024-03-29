<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# CoqEAL

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/coqeal/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/coqeal/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This Coq library contains a subset of the work that was developed in the context
of the ForMath EU FP7 project (2009-2013). It has two parts:
- theory, which contains developments in algebra including normal forms of matrices,
  and optimized algorithms on MathComp data structures.
- refinements, which is a framework to ease change of data representations during a proof.

## Meta

- Author(s):
  - Guillaume Cano (initial)
  - Cyril Cohen (initial)
  - Maxime Dénès (initial)
  - Érik Martin-Dorel
  - Anders Mörtberg (initial)
  - Damien Rouhling
  - Pierre Roux
  - Vincent Siles (initial)
- Coq-community maintainer(s):
  - Cyril Cohen ([**@CohenCyril**](https://github.com/CohenCyril))
  - Pierre Roux ([**@proux01**](https://github.com/proux01))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 or later (use releases for other Coq versions)
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Coq
  - [Paramcoq](https://github.com/coq-community/paramcoq) 1.1.3 or later
  - [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) 1.4.0 or later
  - [MathComp ssreflect](https://math-comp.github.io) 2.1 or later
  - [MathComp algebra](https://math-comp.github.io) 2.1 or later
  - [MathComp Multinomials](https://github.com/math-comp/multinomials) 2.0 or later
  - [MathComp real-closed](https://math-comp.github.io) 2.0 or later
- Coq namespace: `CoqEAL`
- Related publication(s):
  - [A refinement-based approach to computational algebra in Coq](https://hal.inria.fr/hal-00734505/document) doi:[10.1007/978-3-642-32347-8_7](https://doi.org/10.1007/978-3-642-32347-8_7)
  - [Refinements for free!](https://hal.inria.fr/hal-01113453/document) doi:[10.1007/978-3-319-03545-1_10](https://doi.org/10.1007/978-3-319-03545-1_10)
  - [A Coq Formalization of Finitely Presented Modules](https://hal.inria.fr/hal-01378905/document) doi:[10.1007/978-3-319-08970-6_13](https://doi.org/10.1007/978-3-319-08970-6_13)
  - [Formalized Linear Algebra over Elementary Divisor Rings in Coq](https://hal.inria.fr/hal-01081908/document) doi:[10.2168/LMCS-12(2:7)2016](https://doi.org/10.2168/LMCS-12(2:7)2016)
  - [A refinement-based approach to large scale reflection for algebra](https://hal.inria.fr/hal-01414881/document) 
  - [Interaction entre algèbre linéaire et analyse en formalisation des mathématiques](https://tel.archives-ouvertes.fr/tel-00986283/) 
  - [A formal proof of Sasaki-Murao algorithm](https://jfr.unibo.it/article/view/2615) doi:[10.6092/issn.1972-5787/2615](https://doi.org/10.6092/issn.1972-5787/2615)
  - [Formalizing Refinements and Constructive Algebra in Type Theory](http://hdl.handle.net/2077/37325) 
  - [Coherent and Strongly Discrete Rings in Type Theory](https://staff.math.su.se/anders.mortberg/papers/coherent.pdf) doi:[10.1007/978-3-642-35308-6_21](https://doi.org/10.1007/978-3-642-35308-6_21)

## Building and installation instructions

The easiest way to install the latest released version of CoqEAL
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coqeal
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/coqeal.git
cd coqeal
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Theory

The theory directory has the following content:

- `ssrcomplements`, `minor` `mxstructure`, `polydvd`, `similar`,
  `binetcauchy`, `ssralg_ring_tac`: Various extensions of the
  Mathematical Components library.

- `dvdring`, `coherent`, `stronglydiscrete`, `edr`: Hierarchy of
  structures with divisibility (from rings with divisibility, PIDs,
  elementary divisor rings, etc.).

- `fpmod`: Formalization of finitely presented modules.

- `kaplansky`: For providing elementary divisor rings from the
  Kaplansky condition.

- `closed_poly`: Polynomials with coefficients in a closed field.

- `companion`, `frobenius_form`, `jordan`, `perm_eq_image`,
  `smith_complements`: Results on normal forms of matrices.

- `bareiss_dvdring`, `bareiss`, `gauss`, `karatsuba`, `rank`,
  `strassen`, `toomcook`, `smithpid`, `smith`: Various efficient
  algorithms for computing operations on polynomials or matrices.

## Refinements

The refinements directory has the following content:

- `refinements`: Classes for refinements and refines together with
  operational typeclasses for common operations.

- `binnat`: Proof that the binary naturals of Coq (`N`) are a refinement
  of the MathComp unary naturals (`nat`) together with basic operations.

- `binord`: Proof that the binary natural numbers of Coq (`N`) are a refinement
  of the MathComp ordinals.

- `binint`: MathComp integers (`ssrint`) are refined to a new type
  parameterized by positive numbers (represented by a sigma type) and
  natural numbers.  This means that proofs can be done using only
  lemmas from the MathComp library which leads to simpler proofs than
  previous versions of `binint` (e.g., `N`).

- `binrat`: Arbitrary precision rational numbers (`bigQ`) from the
  [Bignums](https://github.com/coq/bignums) library are refined to
  MathComp's rationals (`rat`).

- `rational`: The rational numbers of MathComp (`rat`) are refined to
  pairs of elements refining integers using parametricity of
  refinements.

- `seqmatrix` and `seqmx_complements`: Refinement of MathComp
  matrices (`M[R]_(m,n)`) to lists of lists (`seq (seq R)`).

- `seqpoly`: Refinement of MathComp polynomials (`{poly R}`) to lists (`seq R`).

- `multipoly`: Refinement of
  [MathComp multinomials](https://github.com/math-comp/multinomials)
  and multivariate polynomials to Coq
  [finite maps](https://github.com/coq/coq/blob/master/theories/FSets/FMapAVL.v).

Files should use the following conventions (w.r.t. `Local` and `Global` instances):

```coq
(** Part 1: Generic operations *)
Section generic_operations.

Global Instance generic_operation := ...

(** Part 2: Correctness proof for proof-oriented types and programs *)
Section theory.

Local Instance param_correctness : param ...

(** Part 3: Parametricity *)
Section parametricity.

Global Instance param_parametricity : param ...
Proof. exact: param_trans. Qed.

End parametricity.
End theory.
```
