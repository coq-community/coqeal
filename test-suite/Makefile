#COQBIN := ../../coq/bin/
COQC := $(COQBIN)coqc 
.PHONY: coq clean

all: Parametricity.vo 

examples:: example.vo ListQueue.vo features.vo wadler.vo

Parametricity.vo: Parametricity.v
	$(COQC) -I ../src $<

ListQueue.vo: ListQueue.v Parametricity.vo 
	$(COQC) -I ../src $<

example.vo: example.v Parametricity.vo 
	$(COQC) -I ../src $<

Transport.vo: Transport.v Parametricity.vo 
	$(COQC) -I ../src $<

bug.vo: bug.v Parametricity.vo 
	$(COQC) -debug -I ../src $<

group.vo: group.v Transport.vo Parametricity.vo 
	$(COQC) -I ../src $<

features.vo: features.v Parametricity.vo 
	$(COQC) -I ../src $<

wadler.vo: wadler.v Parametricity.vo 
	$(COQC) -I ../src $<

ide:: Parametricity.vo 
	$(COQBIN)coqide -debug -I ../src *.v 

top:: Parametricity.vo
	$(COQBIN)coqtop -I ../src 

clean:: 
	rm -f *.vo *.glob *.d
