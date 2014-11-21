COQBIN := ../coq/bin/
.PHONY: coq clean

coq:: Makefile.coq
	COQBIN=$(COQBIN) COQDEP=$(COQBIN)coqdep $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	echo "src/abstraction.cmo : src/relations.cmo src/parametricity.cmo src/declare_translation.cmo\nsrc/abstraction.cmx : src/relations.cmx src/parametricity.cmx src/declare_translation.cmx src/abstraction.cmx" > src/abstraction.ml4.d # what's wrong with me ? 
	$(COQBIN)coq_makefile -f Make.cfg -o Makefile.coq

test:: 
	$(COQBIN)coqide -I src test-suite/*.v 

test1: 
	$(COQBIN)coqc -I src test-suite/test1.v 

test2: 
	$(COQBIN)coqc -I src test-suite/test_eq.v 

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.bak .depend
