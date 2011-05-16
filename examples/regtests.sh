#!/bin/sh
# regression tests for why3

TMP=/tmp/why3regtests.out

LOGIC="hello_proof scottish-private-club einstein"
SIMPLE="isqrt mac_carthy gcd gcd_bezout power"
FLOATS="my_cosine"

run_dir () {
    for f in $2; do
	echo -n "Replaying "$1/$f"... "
	if ! why3replayer $1/$f 2>/dev/null > $TMP ; then
	    echo "FAILED:"
	    cat $TMP
	    # exit 1
	else
	    echo "OK"
	fi
    done
}

echo "=== Logic ==="
run_dir . "$LOGIC"
echo ""

echo "=== Simple programs ==="
run_dir programs "$SIMPLE"
echo ""

echo "=== Floating-point programs ==="
run_dir programs "$FLOATS"
echo ""

