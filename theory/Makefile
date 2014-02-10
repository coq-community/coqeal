MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -f Make  -o $(COQMAKEFILE)

dist:
	mkdir CoqEAL_theory
	cp Make.dist CoqEAL_theory/Make
	cat CoqEAL_theory/Make | egrep -v "^#" | egrep ".v$$" | xargs cp -t CoqEAL_theory
	cp -t CoqEAL_theory README
	cp -t CoqEAL_theory INSTALL
	cp -t CoqEAL_theory LICENSE
	cp -t CoqEAL_theory Makefile
	tar zcvf CoqEAL_theory.tgz CoqEAL_theory
	rm -rf CoqEAL_theory

clean: $(COQMAKEFILE)
	$(COQMAKE) clean

install: $(COQMAKEFILE)
	$(COQMAKE) install

%: Makefile.coq
	$(COQMAKE) $@
