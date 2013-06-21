#!/bin/sh
set -e
set -x
COQ2HTML=$COQEAL/../coq2html
make -C makeDot
make -C $COQ2HTML
cd $COQEAL/doc
globs=`ls ../*.glob`
VFILES=`grep -e "^[^ ]*\.v" ../Make`
for i in $VFILES
do
  $COQ2HTML/coq2html -R CoqEAL -o %.html $globs ../$i
done
cd $COQEAL
echo $VFILES | xargs $COQBIN/coqdep -noglob -I . > depend.tmp
sed s/[[:space:]][\-_A-Za-z0-9]*.v.beautified//g depend.tmp > doc/depend
cd $COQEAL/doc
$WORKSPACE/makeDot/makedot depend $COQEALURL
dot -Tpng -o depend.png -Tcmapx -o depend.map depend.dot
dot -Tsvg -o depend.svg depend.dot
