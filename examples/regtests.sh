#!/bin/sh
# regression tests for why3

cd `dirname $0`

TMP=/tmp/why3regtests.out
res=0

run_dir () {
    for f in `ls $1/*/why3session.xml`; do
        d=`dirname $f`
	echo -n "Replaying "$d"... "
	if ! ../bin/why3replayer $d 2>/dev/null > $TMP ; then
	    echo "FAILED:"
	    cat $TMP
	    res=1
	else
	    echo "OK"
	fi
    done
}

echo "=== Logic ==="
run_dir .
echo ""

echo "=== Programs ==="
run_dir programs
echo ""

exit $res


