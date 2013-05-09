#!/bin/bash
samples="25 50 100 150 200 250 500 1000 1500 2000"
rm mulseqmx.dat
touch mulseqmx.dat
for i in $samples
do
  sed "s/#SAMPLE/$i/" < mulseqmx_template.v > tmp.v
  coqtop -R $SSRLIB Ssreflect -I $SSRSRC -R .. CoqEAL -compile tmp | sed -n "s/Finished transaction in [^(]*(\([^u]*\)u.*/$i \1/p" >> mulseqmx.dat
done
