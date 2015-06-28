COQSRC=../../../coq/
COQPLUGIN=../../src
TOOL=bash -x ../../tools/coqdep.sh 

all: Makefile.gen
	make -f Makefile.gen

Makefile.gen graph.dot: 
	$(TOOL) $(COQSRC)

graph.png: graph.dot
	dot -Tpng graph.dot -o graph.png

ide:
	$(COQSRC)/bin/coqide -I $(COQPLUGIN) *.v

clean: Makefile.gen
	make -f Makefile.gen clean
	rm -f Makefile.gen
	rm -f graph.dot graph.png
	rm -f stdlib_*.v
