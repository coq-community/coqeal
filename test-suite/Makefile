COQBIN := ../../coq/bin/
.PHONY: coq clean

all: Parametricity.vo bug.vo

Parametricity.vo: Parametricity.v
	$(COQBIN)coqc -I ../src $<

bug.vo: bug.v Parametricity.vo
	$(COQBIN)coqc -I ../src bug.v 

ide:: 
	$(COQBIN)coqide -I ../src *.v 

clean:: 
	rm -f *.vo *.glob *.d
