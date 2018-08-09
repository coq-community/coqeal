include ../Makefile.common

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

