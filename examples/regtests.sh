#!/bin/sh
# regression tests for why3

REPLAYOPT=""
# Test realization too
CHECK_REALIZATION=""
# Don't test the rest of examples, only the realizations
ONLY_REALIZATION=""

while test $# != 0; do
case "$1" in
  "--force")
        REPLAYOPT="$REPLAYOPT --force"
        ;;
  "--obsolete-only")
        REPLAYOPT="$REPLAYOPT --obsolete-only"
        ;;
  "--prover")
        REPLAYOPT="$REPLAYOPT --prover $2"
        shift
        ;;
  "--check-realizations")
        CHECK_REALIZATION="true"
        ;;
  "--only-realizations")
        ONLY_REALIZATION="true"
        CHECK_REALIZATION="true"
        ;;
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac
shift
done

TMP=$PWD/why3regtests.out
TMPERR=$PWD/why3regtests.err
TMPREAL=/tmp

# Current directory is /examples
cd `dirname $0`

# too early to do that
# REPLAYOPT="$REPLAYOPT --smoke-detector top"

res=0
export success=0
export total=0
export sessions=""
export shapes=""

test_generated () {
  # Current directory is /why3
  mkdir -p $TMPREAL/lib
  echo "Testing isabelle realizations"
  # First copy current realizations in a tmp directory
  cp -r ../lib/isabelle/ $TMPREAL/lib/
  # We want to use the makefile to be sure to check exhaustively the
  # realizations that are built
  make -C .. GENERATED_PREFIX_ISABELLE="$TMPREAL/lib/isabelle" update-isabelle > /dev/null 2> /dev/null
  TMPDIFF=`diff -r -q -x '*.bak' ../lib/isabelle $TMPREAL/lib/isabelle`
  if test "$TMPDIFF" = "" ; then
    printf "Isabelle realizations OK\n"
  else
    printf "ISABELLE REALIZATIONS FAILED, please regenerate and prove them\n"
    printf "$TMPDIFF\n"
    printf "Generated realizations are in /tmp. Use --only-realizations to only test realizations\n"
    res=1
  fi

  echo "Testing coq realizations"
  # First copy current realizations in a tmp directory
  cp -r ../lib/coq/ $TMPREAL/lib/
  # We want to use the makefile to be sure to check exhaustively the
  # realizations that are built
  make -C .. GENERATED_PREFIX_COQ="$TMPREAL/lib/coq" update-coq > /dev/null 2> /dev/null
  TMPDIFF=`diff -r -q -x '*.bak' ../lib/coq $TMPREAL/lib/coq`
  if test "$TMPDIFF" = "" ; then
    printf "Coq realizations OK\n"
  else
    printf "COQ REALIZATIONS FAILED, please regenerate and prove it\n"
    printf "$TMPDIFF\n"
    printf "Generated realizations are in /tmp. Use --only-realizations to only test realizations\n"
    res=1
  fi
}

run_dir () {
    for f in `ls $1/*/why3session.xml`; do
        d=`dirname $f`
        printf "Replaying $d ... "
        ../bin/why3replay.opt -q $REPLAYOPT $2 $d 2> $TMPERR > $TMP
        ret=$?
        if test "$ret" != "0"  ; then
            printf "FAILED (ret code=$ret):"
            out=`head -1 $TMP`
            if test -z "$out" ; then
               echo "standard error: (standard output empty)"
               cat $TMPERR
            else
               cat $TMP
            fi
            res=1
        else
            printf "OK"
            cat $TMP $TMPERR
            success=`expr $success + 1`
        fi
        total=`expr $total + 1`
    done
    sessions="$sessions $1/*/why3session.xml"
    shapes="$shapes $1/*/why3shapes.*"
}

if test "$ONLY_REALIZATION" = "" ; then
    echo "=== Standard Library ==="
    run_dir stdlib
    echo ""

    echo "=== Tests ==="
    # there's no session there...
    # run_dir tests
    run_dir tests-provers
    echo ""

    echo "=== Check Builtin translation ==="
    run_dir check-builtin
    echo ""

    echo "=== BTS ==="
    run_dir bts
    echo ""

    echo "=== Logic ==="
    run_dir logic
    run_dir bitvectors "-L bitvectors"
    echo ""

    echo "=== Programs ==="
    run_dir .
    run_dir foveoos11-cm
    run_dir WP_revisited
    run_dir vacid_0_binary_heaps "-L vacid_0_binary_heaps"
    run_dir avl "-L avl"
    run_dir double_wp "-L double_wp"
    run_dir prover "-L prover"
    echo ""

    echo "Summary       : $success/$total"
    echo "Sessions size : "`wc -cl $sessions | tail -1`
    echo "Shapes   size : "`wc -cl $shapes | tail -1`
fi

if test "$CHECK_REALIZATION" = "true" ; then
    test_generated
fi


exit $res
