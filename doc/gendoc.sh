#!/bin/sh
globs=`ls ../*.glob`
for i in `ls ../*.v`
do
  ~/formathdocs/software/coq2html/coq2html -o %.html $globs $i
done
cd ..
coqdep -noglob -I . *.v > depend
sed s/[[:space:]][[:alnum:]]*.v.beautified//g depend > doc/depend
cd doc
~/coqfinitgroup/trunk/doc/makeDot/makedot depend
dot -Tpng -o depend.png -Tcmapx -o depend.map depend.dot
dot -Tsvg -o depend.svg depend.dot
cat toc.html.head depend.map toc.html.tail > toc.html
#cp *.html depend.* /net/servers/www-sop/members/Maxime.Denes/coqeal
