#!/bin/bash


case "$1" in
  "-mail")
        REPORTBYMAIL=yes;;
  "")
        REPORTBYMAIL=no;;
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac

REPORTDIR=$PWD/..
OUT=$REPORTDIR/nightly-bench.out
PREVIOUS=$REPORTDIR/nightly-bench.previous
DIFF=$REPORTDIR/nightly-bench.diff
REPORT=$REPORTDIR/nightly-bench.report
DATE=`date --utc +%Y-%m-%d`

SUBJECT="Why3 nightly bench:"

notify() {
    if test "$REPORTBYMAIL" == "yes"; then
        mail -s "$SUBJECT" why3-commits@lists.gforge.inria.fr < $REPORT
        # mail -s "$SUBJECT" Claude.Marche@inria.fr < $REPORT
    else
        cat $REPORT
    fi
    exit 0
}


echo "== Why3 bench on $DATE ==" > $REPORT

# configuration
autoconf
./configure --enable-local &> $OUT
if test "$?" != "0" ; then
    echo "Configure failed" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT configure failed"
    notify
else
    echo "Configuration succeeded. " >> $REPORT
fi

# compilation
make -j4 &> $OUT
if test "$?" != "0" ; then
    echo "Compilation failed" >> $REPORT
    tail -20 $OUT >> $REPORT
    SUBJECT="$SUBJECT compilation failed"
    notify
else
    echo "Compilation succeeded. " >> $REPORT
fi

# detection of provers
bin/why3config --detect-provers &> $OUT
if test "$?" != "0" ; then
    echo "Prover detection failed" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT prover detection failed"
    notify
else
    echo "Prover detection succeeded. " >> $REPORT
fi

# increase number of cores used
perl -pi -e 's/running_provers_max = 2/running_provers_max = 4/' why3.conf

# run the bench
make bench &> $OUT
if test "$?" != "0" ; then
    echo "Make bench FAILED" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT make bench failed"
    notify
else
    echo "Make bench succeeded. " >> $REPORT
fi


# replay proofs
examples/regtests.sh &> $OUT
if test "$?" != "0" ; then
    SUBJECT="$SUBJECT failed"
    echo "Proof replay failed" >> $REPORT
else
    SUBJECT="$SUBJECT successful"
    echo " !!! REPLAY SUCCEEDED !!!  YAHOOOO !!! " >> $REPORT
fi

# store the state for this day
cp $OUT $REPORTDIR/regtests-$DATE

# output the diff against previous run
diff -u $PREVIOUS $OUT &> $DIFF
if test "$?" == 0 ; then
    echo "---------- No difference with last bench ---------- " >> $REPORT
else
    echo "" >> $REPORT
    echo "--------------- Diff with last bench --------------" >> $REPORT
    echo "" >> $REPORT
    sed '1,2d' $DIFF >> $REPORT
    cp $OUT $PREVIOUS
fi

# finally print the full state
echo "" >> $REPORT
echo "-------------- Full current state --------------" >> $REPORT
echo "" >> $REPORT
tail -1 $OUT >> $REPORT
echo "" >> $REPORT
cat $OUT >> $REPORT

# final notification after the replay
notify

