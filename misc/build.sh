#!/bin/bash

set -e
eval `opam config env`

# configuration
autoconf
automake --add-missing 2> /dev/null || true
./configure --enable-local

# compilation
make -j2
