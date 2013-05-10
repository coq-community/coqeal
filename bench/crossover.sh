#!/bin/bash
crossover="8 16 32 64 128 256 512"
samples=`seq 50 50 500`
output=crossover.dat
tmp=tmp_crossover
rm $output
touch $output
for j in $crossover
do
  echo "\"crossover = $j\"" >> $output
  for i in $samples
  do
    sed -e "s/#MXSIZE/$i/" -e "s/#CROSSOVER/$j/" < strassen_template.v > $tmp.v
    coqtop -R $SSRLIB Ssreflect -I $SSRSRC -R .. CoqEAL -compile $tmp | sed -n "s/Finished transaction in [^(]*(\([^u]*\)u.*/$i \1/p" >> $output
  done
  echo -e "\n" >> $output
done
