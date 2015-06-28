#!/bin/bash
COQSRC=../../coq
if [ $# -gt 0 ]; then
  COQSRC=$1
fi
PLUGINSRC=../../src
if [ $# -gt 1 ]; then
  PLUGINSRC=$2
fi
THEORIES=$COQSRC
GENDEP=$( dirname "${BASH_SOURCE[0]}")/gendep.py


echo "COQSRC = $COQSRC"
echo "PLUGINSRC = $PLUGINSRC"
echo "GENDEP = $GENDEP"

ARGS=$(find $THEORIES -name "Rdef*.v" | sed 's/^.*coq\///')
ARGS="$ARGS $(find $THEORIES -name "Classical_Prop.v" | sed 's/^.*coq\///')"
modules=$(find $THEORIES -name '*.d' -exec cat '{}' ';' | grep '\.vo[^:]*: ' | python $GENDEP $ARGS)

tmp="/tmp/stdlib.tmp.v"
prefix="stdlib_R"
makefile="Makefile.gen"

for x in $modules; do 
  if [[ $x == *-* ]]; then 
        echo "Parametricity Module $(echo $x | sed 's/-.*$//') as $(echo $x | sed 's/^.*-//')." >> $tmp
  else 
        echo "Parametricity Module $x." >> $tmp
  fi
done
test -f $tmp || exit

split -l 15 -d $tmp $prefix --additional-suffix=.v 
rm -f $tmp

cat > $makefile << EOF 
COQBIN := $COQSRC/bin/
PLUGINSRC := $PLUGINSRC
OPTIONS := -I \$(PLUGINSRC) 
.PHONY: coq clean

SRCS=\$(wildcard *.v)
OBJS=\$(SRCS:.v=.vo)

all: \$(OBJS)

%.vo: %.v
	\$(COQBIN)coqc \$(OPTIONS) \$<

Parametricity.vo: Parametricity.v

clean:
	rm -f *.vo *.glob 

EOF

first="$(printf "$prefix%02d" 0)"
sed -i "1iRequire Parametricity.\nRequire Import $(echo $modules | sed 's/-[a-Z]*[0-9]*_R//g').\n(* Ignoring the following modules : $ARGS. *)" $first.v
echo "$first.vo : $first.v Parametricity.vo" >> $makefile

for x in $(seq 0 100); do 
 y=$(($x + 1))
 prev="$(printf "$prefix%02d" $x)"
 file="$(printf "$prefix%02d" $y)"
 if [ -f "$file.v" ]; then
      sed -i "1iRequire $prev." $file.v
      echo "$file.vo : $file.v $prev.vo" >> $makefile
 fi
done
