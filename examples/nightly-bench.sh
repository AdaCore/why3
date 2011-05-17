#!/bin/bash

OUT=/tmp/nightly-bench.out
REPORT=/tmp/nightly-bench.report

notify() {
    # mail -s "Why3 nightly bench" why3-commits@lists.gforge.inria.fr < $REPORT
    cat $REPORT
    exit 0
}


echo "== Why3 bench on `date` ==" > $REPORT

# phase 1: update the git repository
cd /tmp
# rm -rf why3 
# git clone git://scm.gforge.inria.fr/why3/why3.git

# phase 2: configuration
cd why3
autoconf
./configure --enable-local 2>&1 > $OUT
if test "$?" != "0" ; then
    echo "Configure failed" >> $REPORT
    cat $OUT >> $REPORT
    notify
else 
    echo "Configuration succeeded. " >> $REPORT
fi

# phase 3: compilation
make 2>&1 > $OUT
if test "$?" != "0" ; then
    echo "Compilation failed" >> $REPORT
    tail -20 $OUT >> $REPORT
    notify
else 
    echo "Compilation succeeded. " >> $REPORT
fi

# do we want to do "make bench" ?

# phase 4: replay proofs
examples/regtests.sh 2>&1 > $OUT
if test "$?" != "0" ; then
    echo "Proof replay failed" >> $REPORT
    cat $OUT >> $REPORT
    notify
else 
    echo "Replay succeeded. " >> $REPORT
fi

# final notification if everything is OK
notify

