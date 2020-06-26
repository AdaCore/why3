#!/bin/bash

set -e
if test "$COMPILER" != "system"; then
    opam switch $COMPILER
    eval `opam env`
fi

export OCAMLRUNPARAM=o=20,O=200
./autogen.sh
./configure --enable-local
make

while test $# -gt 0
do
    case "$1" in
        bench)
            bin/why3config --detect
            make bench
            ;;
        ide)
            WHY3CONFIG="" xvfb-run bin/why3 ide --batch="" examples/logic/einstein.why
            bin/why3config --detect
            bench/ide-bench
            ;;
        web_ide)
            make web_ide src/trywhy3/trywhy3.js src/trywhy3/why3_worker.js
            ;;
        doc)
            #make doc # disabled during Sphinx migration
            make stdlibdoc
            make apidoc
            ;;
        ce-bench)
            bin/why3config --detect
            bench/ce-bench
            ;;
        nightly-bench-reduced)
            bin/why3config --detect
            sed -i why3.conf -e "s/running_provers_max = [0-9]*/running_provers_max = 1/"
            cat misc/bench-few-provers-why3-conf >> why3.conf
            COQVER=$(bin/why3 --list-provers | sed -n -e 's/  Coq (\?\([0-9.]\+\).*/\1/p')
            if test "$COQVER" != "" ; then
              sed misc/bench-coq-why3-conf -e "s/@COQVER@/$COQVER/g" >> why3.conf
            fi
            examples/regtests.sh --reduced-mode
            ;;
    esac
    shift
done
