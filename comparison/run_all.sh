#!/bin/sh


PROVERS="spass,eprover,z3,cvc3,simplify,alt-ergo,z3_simple,cvc3_simple,eprover_simple,spass_simple"
#TARGET_DIR="../bench/programs/good/"
TARGET_DIRS="../examples/programs/ ../bench/programs/good/"

for TARGET_DIR in $TARGET_DIRS; do
  for target_file in $TARGET_DIR/*.mlw; do
    echo ./process_file.py $@ "$target_file" "$PROVERS"
    ./process_file.py -C ../why.conf $@ "$target_file" "$PROVERS"
  done
done

