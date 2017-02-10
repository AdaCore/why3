#!/bin/sh
# bench for why3

TMP=$PWD/why3bench.out
TMPERR=$PWD/why3bench.err
cd `dirname $0`

HTML=$PWD/why3bench.html

res=0
export success=0
export total=0

echo '<html>' > $HTML
echo '<head><title>Why3 Bench</title></head>' >> $HTML
echo '<body>' >> $HTML
echo '<h1>Why3 bench</h1>' >> $HTML

run_dir () {
    echo '<h2>Directory '$1'</h2>' >> $HTML
    echo '<ul>' >> $HTML
    for f in `ls $1/*/why3session.xml`; do
        d=`dirname $f`
        b=`basename $d`
	echo -n "Benchmarking $d ... "
        ../bin/why3replay.opt -bench $REPLAYOPT $2 $d 2> $TMPERR > $TMP
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
            echo '<li>'$d' failed' >> $HTML
	else
	    echo "OK"
            success=`expr $success + 1`
            ../bin/why3session html $d 2> $TMPERR > $TMP
            echo '<li><a href="'$d/$b'.html">'$d'</a>' >> $HTML
	fi
        total=`expr $total + 1`
    done
    echo '</ul>' >> $HTML
}

echo "=== Tests ==="
run_dir tests
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
run_dir bitvectors "-I bitvectors"
echo ""

echo "=== Programs ==="
run_dir .
run_dir foveoos11-cm
run_dir WP_revisited
run_dir vacid_0_binary_heaps "-I vacid_0_binary_heaps"
echo ""

echo '</body></html>' >> $HTML
echo "Summary: $success/$total"
exit $res
