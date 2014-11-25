COQPATH := ../../../coq
COQBIN := $(COQPATH)/bin/
COQLIB := $(COQPATH)/
COQDOC := $(COQPATH)/doc/
COQC := $(COQBIN)coqc 
COQMAKE := $(COQBIN)coq_makefile

PLUGINSRC := ../../src

.PHONY: all clean distclean
.SUFFIXES: .vo .v

LIBRARIES := $(wildcard */)

all: Makefile.coq
	make -f $< 

Makefile.coq: Make.cfg
	$(COQMAKE) -f $< -o $@

Make.cfg:
	echo "COQBIN = $(COQBIN)" > $@
	echo "COQLIB = $(COQLIB)" >> $@
	echo "COQDOC = $(COQDOC)" >> $@
	echo "-install none" >> $@
	echo "-I $(PLUGINSRC)" >> $@
	echo "-R . Theories_R" >> $@
	# (for dir in $(LIBRARIES) ; do echo "-R $$dir" ; done) >> $@
	find . -name '*_R.v' -print >> $@
	echo "./Parametricity.v" >> $@


clean:: Makefile.coq
	make -f $< clean

distclean:: clean
	find . -name ".*.aux" -exec rm -f '{}' ';'
	find . -name "*.d" -exec rm -f '{}' ';'
	find . -name ".coq-native" -exec rm -rf '{}' ';'
	rm -f Makefile.coq Make.cfg *.bak
