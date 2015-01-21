COQBIN := ../../coq/bin/
.PHONY: coq clean

all: Parametricity.vo 

Parametricity.vo: Parametricity.v
	$(COQBIN)coqc -I ../src $<

ide:: Parametricity.vo
	$(COQBIN)coqide -I ../src *.v 

clean:: 
	rm -f *.vo *.glob *.d
