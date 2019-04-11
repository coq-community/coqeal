CoqEAL - The Coq Effective Algebra Library
==========================================

This repository contains a subset of the work that was developed in
the context of the ForMath european project (2009-2013), and was extended afterwards.
This archive is split in four parts:

- theory (package  CoqEAL.theory), which contains  formal developments
  in algebra and optimized algorithms on mathcomp data structures.

- refinements (package  CoqEAL.refinements), which is a framework to 
  ease change of data representation during a proof.

- doc, tools for generating documentation out of local documentation.


Authors
=======

Guillaume Cano,  Cyril Cohen,  Maxime Dénès, Anders Mörtberg, Damien Rouhling and Vincent
Silès.

Compilation & Installation
==========================

Assuming your opam is installed and initialized
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```
  
Dependencies
============

coq >= 8.7
coq-paramcoq >= 1.1.1
coq-mathcomp-ssreflect >= 1.8.0
coq-mathcomp-fingroup >= 1.8.0
coq-mathcomp-algebra >= 1.8.0
coq-mathcomp-finmap >= 1.2.0
coq-mathcomp-bigenough >= 1.0.0
coq-mathcomp-multinomials >= 1.2
