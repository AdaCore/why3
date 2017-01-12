#!/bin/sh

GMP_DIR="${HOME}/gmp_gen"
export LD_LIBRARY_PATH=${GMP_DIR}/lib:$LD_LIBRARY_PATH
export LIBRARY_PATH=${GMP_DIR}/lib:$LIBRARY_PATH
export CPATH=${GMP_DIR}/include:$CPATH
