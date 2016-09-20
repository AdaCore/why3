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
	echo -n "Replaying $d ... "
        ../bin/why3replay.opt -q $REPLAYOPT $2 $d 2> $TMPERR > $TMP
        ret=$?
	if test "$ret" != "0"  ; then
	    echo -n "FAILED (ret code=$ret):"
            out=`head -1 $TMP`
            if test -z "$out" ; then
               echo "standard error: (standard output empty)"
               cat $TMPERR
            else
	       cat $TMP
            fi
	    res=1
	else
	    echo -n "OK"
	    cat $TMP $TMPERR
            success=`expr $success + 1`
	fi
        total=`expr $total + 1`
    done
    sessions="$sessions $1/*/why3session.xml"
    shapes="$shapes $1/*/why3shapes.*"
}

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
echo ""

echo "Summary       : $success/$total"
echo "Sessions size : "`wc -cl $sessions | tail -1`
echo "Shapes   size : "`wc -cl $shapes | tail -1`

exit $res
