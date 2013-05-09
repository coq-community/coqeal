#!/bin/bash
samples="25 50 100 150 200 250 500 1000 1500 2000"
rm strassen.dat
touch strassen.dat
for i in $samples
do
  sed "s/#SAMPLE/$i/" < strassen_template.v > tmp.v
  coqtop -R $SSRLIB Ssreflect -I $SSRSRC -R .. CoqEAL -compile tmp | sed -n "s/Finished transaction in [^(]*(\([^u]*\)u.*/$i \1/p" >> strassen.dat
done
