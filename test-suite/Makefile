COQBIN := ../../coq/bin/
.PHONY: coq clean

all: Parametricity.vo Theories_R.vo Ring_polynom_R.vo bug.vo

Theories_R.vo: Theories_R.v Parametricity.vo
	$(COQBIN)coqc -I ../src $<

Ring_polynom_R.vo: Ring_polynom_R.v Theories_R.vo Theories_R.vo 
	$(COQBIN)coqc -I ../src $<

Parametricity.vo: Parametricity.v
	$(COQBIN)coqc -I ../src $<

bug.vo: bug.v 
	$(COQBIN)coqc -I ../src bug.v 

ide:: 
	$(COQBIN)coqide -I ../src *.v 

clean:: 
	rm -f *.vo *.glob *.d
