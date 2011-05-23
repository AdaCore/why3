#!/bin/sh
# regression tests for why3

TMP=$PWD/why3regtests.out
TMPERR=$PWD/why3regtests.err

cd `dirname $0`

res=0

run_dir () {
    for f in `ls $1/*/why3session.xml`; do
        d=`dirname $f`
	echo -n "Replaying "$d"... "
        ../bin/why3replayer.opt $d 2> $TMPERR > $TMP
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
	    cat $TMP
	fi
    done
}

echo "=== Logic ==="
run_dir .
echo ""

echo "=== BTS ==="
run_dir bts
echo ""

echo "=== Programs ==="
run_dir programs
echo ""

echo "=== Check Builtin translation ==="
run_dir check-builtin
echo ""

exit $res


