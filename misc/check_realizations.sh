

# cd to the directory of this script
cd `dirname $0`

# temporary directory where we generate realizations
TMPREAL=$(mktemp -d /tmp/why3realizations-XXXXXXX)
mkdir -p $TMPREAL/lib


echo "Testing isabelle realizations"
# First copy current realizations in a tmp directory
cp -r ../lib/isabelle/ $TMPREAL/lib/
# We want to use the makefile to be sure to check exhaustively the
# realizations that are built
make -C .. GENERATED_PREFIX_ISABELLE="$TMPREAL/lib/isabelle" update-isabelle > /dev/null 2> /dev/null
TMPDIFF=`diff -r -q -x '*.bak' -x '*~' -x '*.aux' ../lib/isabelle $TMPREAL/lib/isabelle`
if test "$TMPDIFF" = "" ; then
    printf "Isabelle realizations OK\n"
else
    printf "ISABELLE REALIZATIONS FAILED, please regenerate and prove them\n"
    printf "$TMPDIFF\n"
    printf "Generated realizations are in $TMPREAL\n"
    res=1
fi

echo "Testing coq realizations"
# First copy current realizations in a tmp directory
cp -r ../lib/coq/ $TMPREAL/lib/
# We want to use the makefile to be sure to check exhaustively the
# realizations that are built
make -C .. GENERATED_PREFIX_COQ="$TMPREAL/lib/coq" update-coq > /dev/null 2> /dev/null
TMPDIFF=`diff -r -q -x '*.bak' -x '*~' -x '*.aux'  ../lib/coq $TMPREAL/lib/coq`
if test "$TMPDIFF" = "" ; then
    printf "Coq realizations OK\n"
else
    printf "COQ REALIZATIONS FAILED, please regenerate and prove it\n"
    printf "$TMPDIFF\n"
    printf "Generated realizations are in $TMPREAL\n"
    res=1
fi
