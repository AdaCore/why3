#!/bin/sh
# bench for why3

TMP=$PWD/why3bench.out
TMPERR=$PWD/why3bench.err
HTML=$PWD/why3bench.html

cd `dirname $0`


res=0
export success=0
export total=0

echo '<html>' > $HTML
echo '<head><title>Why3 Bench</title></head>' >> $HTML
echo '<body>' > $HTML
echo '<h1>Why3 bench</h1>' > $HTML
 
run_dir () {
    echo '<h2>Directory '$1'</h2>' > $HTML
    echo '<ul>' > $HTML
    for f in `ls $1/*/why3session.xml`; do
        d=`dirname $f`
	echo -n "Benchmarking $d ... "
        ../bin/why3replayer.opt -bench $REPLAYOPT $2 $d 2> $TMPERR > $TMP
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
            echo '<li>'$d' failed'
	else
	    echo -n "OK"
            ../bin/why3session -bench $d 2> $TMPERR > $TMP
            echo '<li><a href="'$d'">'$d'</a>'
	    cat $TMP
            success=`expr $success + 1`
	fi
        total=`expr $total + 1`
    done
    echo '</ul>' > $HTML
}

echo "=== Logic ==="
run_dir .
echo ""

# echo "=== BTS ==="
# run_dir bts
# echo ""

# echo "=== Programs ==="
# run_dir programs
# echo ""

# echo "=== Programs in their own subdir ==="
# run_dir programs/vacid_0_binary_heaps "-I programs/vacid_0_binary_heaps"
# run_dir hoare_logic "-I hoare_logic"
# echo ""

# echo "=== Check Builtin translation ==="
# run_dir check-builtin
# echo ""

echo "Summary: $success/$total"
exit $res



