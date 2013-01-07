#!/bin/sh
globs=`ls ../*.glob`
for i in `ls ../*.v`
do
  ~/formathdocs/software/coq2html/coq2html -o %.html $globs $i
done
coqdep -noglob -I . ../*.v > depend
~/coqfinitgroup/trunk/doc/makeDot/makedot depend
dot -Tpng -o depend.png -Tcmapx -o depend.map depend.dot
dot -Tsvg -o depend.svg depend.dot
