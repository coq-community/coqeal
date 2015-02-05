THEORIES=../../coq/theories/

modules=$(find $THEORIES -name "*.d" -exec cat '{}' ';' | python gendep.py)

echo "Require Import $modules."
for x in $modules; do 
  echo "Translate Module $x."
done
