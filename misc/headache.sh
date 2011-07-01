#!/bin/sh

headache -c misc/headache_config.txt -h misc/header.txt "$@"

headache -c misc/headache_config.txt -h misc/header_gm.txt \
    src/transform/abstraction.ml* \
    src/transform/simplify_formula.ml* \
    src/printer/gappa.ml*

headache -c misc/headache_config.txt -h misc/header_jk.txt \
    src/transform/close_epsilon.ml* \
    src/transform/lift_epsilon.ml*

headache -c misc/headache_config.txt -h misc/header_sc.txt \
    src/transform/hypothesis_selection.ml* \
    src/tptp2why/*.ml*

sed -i -e '
    s/Francois Bobot/François Bobot/g;
    s/Jean-Christophe Filliatre/Jean-Christophe Filliâtre/g;
    s/Claude Marche/Claude Marché/g' -- "$@"

