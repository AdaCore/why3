#!/bin/sh
# regression tests for why3

case "$1" in
  "-force")
        REPLAYOPT="-force"
        ;;
  "-obsolete-only")
        REPLAYOPT="-obsolete-only -force"
        ;;
  "")
        REPLAYOPT=""
        ;;
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac

TMP=$PWD/why3regtests.out
TMPERR=$PWD/why3regtests.err

cd `dirname $0`

# too early to do that
# REPLAYOPT="$REPLAYOPT -smoke-detector top"

res=0
export success=0
export total=0

run_dir () {
    for f in `ls $1/*/why3session.xml`; do
        d=`dirname $f`
	echo -n "Replaying $d ... "
        ../bin/why3replayer.opt -q $REPLAYOPT $2 $d 2> $TMPERR > $TMP
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
}


echo "=== Logic ==="
run_dir .
echo ""

echo "=== Tests Provers ==="
run_dir tests-provers
echo ""

echo "=== Check Builtin translation ==="
run_dir check-builtin
echo ""

echo "=== BTS ==="
run_dir bts
echo ""

echo "=== Programs ==="
run_dir programs
echo ""

echo "=== Programs in their own subdir ==="
run_dir programs/vacid_0_binary_heaps "-I programs/vacid_0_binary_heaps"
run_dir hoare_logic "-I hoare_logic"
run_dir bitvectors "-I bitvectors"
run_dir foveoos2011 "-I foveoos2011"
echo ""

echo "Summary: $success/$total"
exit $res



