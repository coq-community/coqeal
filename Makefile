.PHONY: coq clean

coq:: Makefile.coq
	COQBIN=$(COQBIN) COQDEP=$(COQBIN)coqdep $(MAKE) -f Makefile.coq

src/paramcoq_mod.ml: src/paramcoq.mllib
	sed -e "s/\([^ ]\{1,\}\)/let _=Mltop.add_known_module\"\1\" /g" $< > $@
	echo "let _=Mltop.add_known_module\"paramcoq\"" >> $@

Makefile.coq: Make.cfg src/paramcoq_mod.ml
	$(COQBIN)coq_makefile -f Make.cfg -o Makefile.coq
	sed -i 's/$$(COQDEP) $$(OCAMLLIBS)/$$(COQDEP) $$(OCAMLLIBS) -c/' Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f src/paramcoq_mod.ml

distclean:
	rm -f Makefile.coq Makefile.coq.bak .depend
