Compilation
===========

1. Replace COQBIN in the Makefile with a path to the latest trunk. 
2. Make. 
3. ????
4. Profit. 

Available commands
==================

The default arity is 2. 
The default name is automatically generated when translating a constant (otherwise you need to provide it). 

- Translate *term* [as *name*] [arity *n*]. 

Define a new constant named *name* obtained by computing the parametricity translation of *term*. 

- Translate Inductive *inductive* [as *name*] [arity *n*].

Declare a new inductive type named *name* from the translation of *inductive*. 

- Realizer *constant or variable* [as *name*] [arity *n*] := *term*.

Declare *term* to be the translation of a constant. 
Useful to translate terms containing section variables, or axioms. 
