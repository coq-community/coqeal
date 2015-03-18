COQBIN := ../coq/bin/
.PHONY: coq clean

coq:: Makefile.coq
	COQBIN=$(COQBIN) COQDEP=$(COQBIN)coqdep $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
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
