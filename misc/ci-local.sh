#!/bin/bash

function section_start()
{ echo -e "\e[0Ksection_start:`date +%s`:$1[collapsed=true]\r\e[0K\e[32;1m$2\e[0;m"; }
function section_stop()
{ echo -e "\e[0Ksection_end:`date +%s`:$1\r\e[0K"; }

set -e
if test "$COMPILER" != "system"; then
    opam switch $COMPILER
    eval `opam env`
fi

export OCAMLRUNPARAM=o=20,O=200

section_start configure Configuration
./autogen.sh
./configure --enable-local
section_stop configure

section_start build Building
make
section_stop build

while test $# -gt 0
do
    section_start "test_$1" "Testing \"$1\""
    case "$1" in
        bench)
            bin/why3 config detect
            make bench
            ;;
        ide)
            WHY3CONFIG="" xvfb-run bin/why3 ide --batch="" examples/logic/einstein.why
            bin/why3 config detect
            bench/ide-bench
            ;;
        web_ide)
            make web_ide trywhy3
            ;;
        doc)
            make predoc
            make stdlibdoc
            make apidoc
            ;;
        ce-bench)
            bin/why3 config detect
            bench/ce-bench
            bench/check-ce-bench
            ;;
        nightly-bench-reduced)
            bin/why3 config detect
            sed -i why3.conf -e "s/running_provers_max = [0-9]*/running_provers_max = 1/"
            cat misc/bench-few-provers-why3-conf >> why3.conf
            COQVER=$(bin/why3 config list-provers | sed -n -e 's/Coq (\?\([0-9.]\+\).*/\1/p')
            if test "$COQVER" != "" ; then
              sed misc/bench-coq-why3-conf -e "s/@COQVER@/$COQVER/g" >> why3.conf
            fi
            examples/regtests.sh --reduced-mode
            ;;
    esac
    section_stop "test_$1"
    shift
done
