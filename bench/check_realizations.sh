#!/bin/bash

# temporary directory where we generate realizations
TMPREAL=$(mktemp -d /tmp/why3realizations-XXXXXXX)
mkdir -p $TMPREAL/lib
res=0

echo "Testing Isabelle realizations"
# First copy current realizations in a tmp directory
cp -r lib/isabelle $TMPREAL/lib/
# We want to use the makefile to be sure to check exhaustively the
# realizations that are built
make GENERATED_PREFIX_ISABELLE="$TMPREAL/lib/isabelle" update-isabelle > /dev/null 2> /dev/null
LANG=C diff -r -q -x '*.bak' -x '*~' -x '*.aux' lib/isabelle $TMPREAL/lib/isabelle > $TMPREAL/diff-isabelle
if test -s "$TMPREAL/diff-isabelle"; then
    echo "Isabelle realizations FAILED, please regenerate and prove them"
    sed -e "s,$TMPREAL/lib/isabelle,new," $TMPREAL/diff-isabelle
    res=1
else
    echo "Isabelle realizations OK"
fi

echo "Testing Coq realizations"
# First copy current realizations in a tmp directory
cp -r lib/coq $TMPREAL/lib/
# We want to use the makefile to be sure to check exhaustively the
# realizations that are built
make GENERATED_PREFIX_COQ="$TMPREAL/lib/coq" update-coq > /dev/null 2> /dev/null
LANG=C diff -r -q -x '*.bak' -x '*~' -x '*.aux' lib/coq $TMPREAL/lib/coq > $TMPREAL/diff-coq
if test -s "$TMPREAL/diff-coq"; then
    echo "Coq realizations FAILED, please regenerate and prove them"
    sed -e "s,$TMPREAL/lib/coq,new," $TMPREAL/diff-coq
    res=1
else
    echo "Coq realizations OK"
fi

rm -r $TMPREAL
exit $res
