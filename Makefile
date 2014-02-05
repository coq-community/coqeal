MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	/bin/mkdir -p bin
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -f Make  -o $(COQMAKEFILE)

dist:
	mkdir CoqEAL
	cp Make.dist CoqEAL/Make
	cat CoqEAL/Make | egrep -v "^#" | egrep ".v$$" | xargs cp -t CoqEAL
	cp -t CoqEAL README
	cp -t CoqEAL INSTALL
	cp -t CoqEAL LICENSE
	cp   Makefile.dist    CoqEAL/Makefile
	tar zcvf CoqEAL.tgz CoqEAL
	rm -rf CoqEAL

clean: $(COQMAKEFILE)
	$(COQMAKE) clean
	$(RM) -rf bin $(COQMAKEFILE)

%: Makefile.coq
	$(COQMAKE) $@
