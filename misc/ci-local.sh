#!/bin/bash

set -e
eval `opam config env`

export OCAMLRUNPARAM=o=20,O=200
./configure --enable-local
make

while test $# -gt 0
do
    case "$1" in
        bench)
            bin/why3config --detect-provers
            make bench
            ;;
        ide)
            WHY3CONFIG="" xvfb-run bin/why3 ide --batch "" examples/logic/einstein.why
            ;;
        doc)
            make doc
            ;;
        ce-bench)
            bin/why3config --detect-provers
            bench/ce-bench
            ;;
        nightly-bench-reduced)
            bin/why3config --detect-provers
            sed -i why3.conf -e "s/running_provers_max = [0-9]*/running_provers_max = 1/"
            cat misc/bench-few-provers-why3-conf >> why3.conf
            examples/regtests.sh --reduced-mode
            ;;
    esac
    shift
done
