COQBIN := ../coq/bin/
.PHONY: coq clean

coq:: Makefile.coq
	COQBIN=$(COQBIN) $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	$(COQBIN)/coq_makefile -f Make.cfg -o Makefile.coq

test:: coq
	$(COQBIN)/coqide -I src test-suite/test1.v

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.bak .depend
