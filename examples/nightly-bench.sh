#!/bin/bash

REPORTDIR=$PWD/..
OUT=$REPORTDIR/nightly-bench.out
PREVIOUS=$REPORTDIR/nightly-bench.previous
DIFF=$REPORTDIR/nightly-bench.diff
REPORT=$REPORTDIR/nightly-bench.report
DATE=`date --utc +%Y-%m-%d`

notify() {
    mail -s "Why3 nightly bench" why3-commits@lists.gforge.inria.fr < $REPORT
    # mail -s "test Why3 nightly bench" Claude.Marche@inria.fr < $REPORT
    # cat $REPORT
    exit 0
}


echo "== Why3 bench on $DATE ==" > $REPORT

# configuration
autoconf
./configure --enable-local &> $OUT
if test "$?" != "0" ; then
    echo "Configure failed" >> $REPORT
    cat $OUT >> $REPORT
    notify
else
    echo "Configuration succeeded. " >> $REPORT
fi

# compilation
make -j4 &> $OUT
if test "$?" != "0" ; then
    echo "Compilation failed" >> $REPORT
    tail -20 $OUT >> $REPORT
    notify
else
    echo "Compilation succeeded. " >> $REPORT
fi

# detection of provers
bin/why3config --detect-provers &> $OUT
if test "$?" != "0" ; then
    echo "Prover detection failed" >> $REPORT
    cat $OUT >> $REPORT
    notify
else
    echo "Prover detection succeeded. " >> $REPORT
fi

# increase number of cores used
perl -pi -e 's/running_provers_max = 2/running_provers_max = 4/' why.conf

# do we want to do "make bench" ?

# replay proofs
examples/regtests.sh &> $OUT
if test "$?" != "0" ; then
    cp $OUT $REPORTDIR/regtests-$DATE
    echo "Proof replay failed" >> $REPORT
    diff -u $PREVIOUS $OUT &> $DIFF
    if test "$?" == 0 ; then
        echo "---------- No difference with last bench ---------- " >> $REPORT
        echo "" >> $REPORT
        echo "-------------- Full current state --------------" >> $REPORT
        echo "" >> $REPORT
        cat $OUT >> $REPORT
    else
        echo "" >> $REPORT
        echo "--------------- Diff with last bench --------------" >> $REPORT
        echo "" >> $REPORT
        sed '1,2d' $DIFF >> $REPORT
        cp $OUT $PREVIOUS
        echo "" >> $REPORT
        echo "-------------- Full current state --------------" >> $REPORT
        echo "" >> $REPORT
        cat $OUT >> $REPORT
    fi
    notify
else
    echo "Replay succeeded. " >> $REPORT
fi

# final notification if everything is OK
notify

