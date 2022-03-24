#!/bin/bash

set -e

for f in "$@"; do opam pin -n add $f .; done
for f in "$@"; do opam install -j2 -v $f; done

opam exec -- ocamlfind ocamlopt -package why3 -o test -linkpkg misc/test_lib.ml
