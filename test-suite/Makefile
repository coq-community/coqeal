COQBIN := ../../coq/bin/
.PHONY: coq clean

all: Parametricity.vo 

examples:: example.vo ListQueue.vo features.vo wadler.vo

Parametricity.vo: Parametricity.v
	$(COQBIN)coqc -I ../src $<

ListQueue.vo: ListQueue.v Parametricity.vo 
	$(COQBIN)coqc -I ../src $<

example.vo: example.v Parametricity.vo 
	$(COQBIN)coqc -I ../src $<

features.vo: features.v Parametricity.vo 
	$(COQBIN)coqc -I ../src $<

wadler.vo: wadler.v Parametricity.vo 
	$(COQBIN)coqc -I ../src $<

ide:: Parametricity.vo
	$(COQBIN)coqide -I ../src *.v 

clean:: 
	rm -f *.vo *.glob *.d
