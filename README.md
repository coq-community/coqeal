<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# CoqEAL

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/CoqEAL/coqeal/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/CoqEAL/coqeal/actions?query=workflow:"Docker%20CI"




This libary contains a subset of the work that was developed in the context of the ForMath european project (2009-2013). It has two parts:
- theory (module CoqEAL_theory), which contains formal developments in algebra and optimized algorithms on mathcomp data structures.
- refinements (module CoqEAL_refinements), which is a framework to ease change of data representation during a proof.

## Meta

- Author(s):
  - Guillaume Cano (initial)
  - Cyril Cohen (initial)
  - Maxime Dénès (initial)
  - Anders Mörtberg (initial)
  - Damien Rouhling
  - Vincent Siles (initial)
- License: [MIT](LICENSE)
- Compatible Coq versions: 8.10 or later (use releases for other Coq versions)
- Additional dependencies:
  - [Bignums](https://github.com/coq/bignums) same version as Coq
  - [Paramcoq](https://github.com/coq-community/paramcoq) 1.1.1 or later
  - [MathComp Multinomials](https://github.com/math-comp/multinomials) >= 1.5.1 and < 1.7
  - [MathComp](https://math-comp.github.io) 1.12.0 or newer
- Coq namespace: `CoqEAL`
- Related publication(s):
  - [A refinement-based approach to computational algebra in Coq](https://hal.inria.fr/hal-00734505/document) doi:[10.1007/978-3-642-32347-8_7](https://doi.org/10.1007/978-3-642-32347-8_7)
  - [Refinements for free!](https://hal.inria.fr/hal-01113453/document) doi:[10.1007/978-3-319-03545-1_10](https://doi.org/10.1007/978-3-319-03545-1_10)
  - [A Coq Formalization of Finitely Presented Modules](https://hal.inria.fr/hal-01378905/document) doi:[10.1007/978-3-319-08970-6_13](https://doi.org/10.1007/978-3-319-08970-6_13)
  - [Formalized Linear Algebra over Elementary Divisor Rings in Coq](https://hal.inria.fr/hal-01081908/document) doi:[10.2168/LMCS-12(2:7)2016](https://doi.org/10.2168/LMCS-12(2:7)2016)
  - [A refinement-based approach to large scale reflection for algebra](https://hal.inria.fr/hal-01414881/document) 

## Building and installation instructions

The easiest way to install the latest released version of CoqEAL
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coqeal
```

To instead build and install manually, do:

``` shell
git clone https://github.com/CoqEAL/coqeal.git
cd coqeal
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Additional directories

- doc: tools for generating documentation out of local documentation.

- releases: archives of pre-GitHub releases
