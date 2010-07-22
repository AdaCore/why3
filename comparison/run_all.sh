#!/bin/sh

# lance les prouveurs donnés (ou ceux donnés en argument) sur les fichiers de 2 dossiers

PROVERS="spass,eprover,z3,cvc3,simplify,alt-ergo,z3_simple,cvc3_simple,eprover_simple,spass_simple"

if [ -n $1 ]; then
  PROVERS="$1"
  echo "utilise les prouveurs $1"
fi

TARGET_DIRS="../examples/programs/ ../bench/programs/good/"

for TARGET_DIR in $TARGET_DIRS; do
  for target_file in $TARGET_DIR/*.mlw; do
    echo ./process_file.py "$target_file" "$PROVERS"
    ./process_file.py -C ../why.conf "$target_file" "$PROVERS"
  done
done

