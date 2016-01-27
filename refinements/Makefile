MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

dist:
	mkdir CoqEAL_refinements
	cp Make.dist CoqEAL_refinements/_CoqProject
	cat CoqEAL_refinements/_CoqProject | egrep -v "^#" | egrep ".v$$" | xargs cp -t CoqEAL_refinements
	cp -t CoqEAL_refinements README
	cp -t CoqEAL_refinements INSTALL
	cp -t CoqEAL_refinements LICENSE
	cp -t CoqEAL_refinements Makefile
	tar zcvf CoqEAL_refinements.tgz CoqEAL_refinements
	rm -rf CoqEAL_refinements

clean: $(COQMAKEFILE)
	$(COQMAKE) clean

install: $(COQMAKEFILE)
	$(COQMAKE) install

%: Makefile.coq
	$(COQMAKE) $@
