MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	/bin/mkdir -p bin
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -arg "-I $(SSRSRC) -I $(SSRLIB)" -f Make  -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(COQMAKE) clean
	$(RM) -rf bin $(COQMAKEFILE)

%: Makefile.coq
	$(COQMAKE) $@
