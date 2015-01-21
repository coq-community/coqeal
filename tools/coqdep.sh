THEORIES=../../coq/



modules=$(find $THEORIES -name "*.d" -exec cat '{}' ';' | sed ':a;N;$!ba;s/\\\s*\n/ /g' | python gendep.py)

echo "Require Import $modules."
for x in $modules; do 
  echo "Translate Module $x."
done
