#!/bin/bash
samples="25 100 200 500 750 1000 1200 1400 1600 1800 2000 2200 2500 3000"
crossover=256
output=strassen.dat
tmp=tmp_strassen
if [ -f $output ]
then
  rm $output
fi
touch $output
for i in $samples
do
  sed -e "s/#MXSIZE/$i/" -e "s/#CROSSOVER/$crossover/" < strassen_template.v > $tmp.v
  coqtop -R $SSRLIB Ssreflect -I $SSRSRC -R .. CoqEAL -compile $tmp | sed -n "s/Finished transaction in [^(]*(\([^u]*\)u.*/$i \1/p" >> $output
done
