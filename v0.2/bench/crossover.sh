#!/bin/bash
crossover="16 32 64 128 256 512"
sizes="2048 2047"
output=crossover.dat
tmp=tmp_crossover
rm $output
touch $output
for j in $sizes
do
  echo "\"$jx$j\"" >> $output
  for i in $crossover
  do
    sed -e "s/#MXSIZE/$j/" -e "s/#CROSSOVER/$i/" < strassen_template.v > $tmp.v
    coqtop -R $SSRLIB Ssreflect -I $SSRSRC -R .. CoqEAL -compile $tmp | sed -n "s/Finished transaction in [^(]*(\([^u]*\)u.*/$i \1/p" >> $output
  done
  echo -e "\n" >> $output
done
