#!/bin/bash

OUT=/tmp/nightly-bench.out
REPORT=/tmp/nightly-bench.report

notify() {
    mail -s "Why3 nightly bench" why3-commits@lists.gforge.inria.fr < $REPORT
    # cat $REPORT
    exit 0
}


echo "== Why3 bench on `date` ==" > $REPORT

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

# do we want to do "make bench" ?

# replay proofs
examples/regtests.sh &> $OUT
if test "$?" != "0" ; then
    echo "Proof replay failed" >> $REPORT
    cat $OUT >> $REPORT
    notify
else 
    echo "Replay succeeded. " >> $REPORT
fi

# final notification if everything is OK
notify

