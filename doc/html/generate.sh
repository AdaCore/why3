#!/bin/bash

# disclaimer : this script is very ugly !

PREFIX=$( dirname $0 )

echo "must be in $PREFIX/trunk/doc/html/"
cd $PREFIX/../../src/
echo "currently in $PWD"

# find dirs to include to find .cmi
DIRS=$( find -type d -not -wholename '*.svn*' -printf "%p " )
INCLUDES=$( find -type d -not -wholename '*.svn*' | while read i ; do echo -n "-I $i "; done )
BACK_INCLUDES=$( for i in $DIRS; do echo -n "-I ../$i "; done )
ALL_TARGETS=$( find -name '*.ml' -or -name '*.mli' -printf "%p " )

# for tests
echo "$DIRS"
echo "$INCLUDES"
echo "$ALL_TARGETS"
#echo "$BACK_INCLUDES"

TARGET_DIR=../doc/html/
ocamldoc -d $TARGET_DIR ${INCLUDES} -I /usr/lib/ocaml/ -html $ALL_TARGETS
