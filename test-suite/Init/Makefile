COQBIN := ../../../coq/bin/
COQC := $(COQBIN)coqc -I ../../src
.PHONY: all clean
.SUFFIXES: .vo .v
all:: Parametricity.vo Logic_R.vo Datatypes_R.vo Nat_R.vo Peano_R.vo Specif_R.vo Wf_R.vo

Parametricity.vo: Parametricity.v
Logic_R.vo: Logic_R.v 
Datatypes_R.vo: Datatypes_R.v
Nat_R.vo: Nat_R.v Logic_R.vo Datatypes_R.vo
Peano_R.vo: Peano_R.vo Nat_R.vo
Specif_R.vo: Specif_R.v Logic_R.vo Datatypes_R.vo
Wf_R.vo: Wf_R.v Logic_R.vo Datatypes_R.vo

.v.vo: 
	$(COQC) $<

ide:: 
	$(COQBIN)coqide -I ../../src *.v 

clean:: 
	rm -f *.vo *.glob *.d
