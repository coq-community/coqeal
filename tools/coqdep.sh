THEORIES=../../coq/theories/


ARGS=$(find $THEORIES -name "Rdef*.v" | sed 's/..\/..\/coq\///g')
ARGS="$ARGS $(find $THEORIES -name "Classical_Prop.v" | sed 's/..\/..\/coq\///g')"
modules=$(find $THEORIES -name "*.d" -exec cat '{}' ';' | python gendep.py $ARGS)

echo "Require Import $modules."
for x in $modules; do 
  echo "Translate Module $x."
done
