#!/bin/sh
# regression tests for why3

REPLAYOPT=""

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
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac
shift
done

TMP=$PWD/why3regtests.out
TMPERR=$PWD/why3regtests.err

# Current directory is /examples
cd `dirname $0`

# too early to do that
# REPLAYOPT="$REPLAYOPT --smoke-detector top"

res=0
export success=0
export total=0
export sessions=""
export shapes=""


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

echo "=== Programs already ported === MUST REPLAY AND ALL GOALS PROVED ==="
echo ""
run_dir .
run_dir double_wp "-L double_wp"
run_dir avl "-L avl"
run_dir foveoos11-cm
run_dir vacid_0_binary_heaps "-L vacid_0_binary_heaps"
run_dir verifythis_2016_matrix_multiplication "-L verifythis_2016_matrix_multiplication"
run_dir WP_revisited
run_dir prover "-L prover --debug ignore_unused_vars"
echo ""

echo "Score on ported programs : $success/$total"
echo ""

echo "=== Standard Library ==="
echo ""
run_dir stdlib
echo ""

echo "=== Tests ==="
echo ""
# there's no session there...
# run_dir tests
run_dir tests-provers
echo ""

echo "=== Check Builtin translation ==="
echo ""
run_dir check-builtin
echo ""

echo "=== BTS ==="
echo ""
run_dir bts
echo ""

echo "=== Logic ==="
echo ""
run_dir logic
run_dir bitvectors "-L bitvectors"
echo ""

echo "Summary       : $success/$total"
echo "Sessions size : "`wc -cl $sessions | tail -1`
echo "Shapes   size : "`wc -cl $shapes | tail -1`

exit $res
