.PHONY: coq clean

coq:: Makefile.coq
	$(MAKE) -f Makefile.coq

src/paramcoq_mod.ml: src/paramcoq.mlpack
	sed -e "s/\([^ ]\{1,\}\)/let _=Mltop.add_known_module\"\1\" /g" $< > $@
	echo "let _=Mltop.add_known_module\"paramcoq\"" >> $@

Makefile.coq: Make.cfg src/paramcoq_mod.ml
	coq_makefile -f Make.cfg -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean

distclean:
	rm -f Makefile.coq Makefile.coq.bak .depend

# if using opam, this installs paramcoq at the right place: ~/.opam/...
# otherwise, use with sudo for a systemwide install
install:
	$(MAKE) -f Makefile.coq install
