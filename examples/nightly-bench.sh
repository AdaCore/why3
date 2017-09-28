#!/bin/bash


case "$1" in
  "-mail")
        REPORTBYMAIL=$2;;
  "")
        REPORTBYMAIL=no;;
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac

REPORTDIR=$PWD/../why3-itp-reports
OUT=$REPORTDIR/nightly-bench.out
PREVIOUS=$REPORTDIR/nightly-bench.previous
DIFF=$REPORTDIR/nightly-bench.diff
REPORT=$REPORTDIR/nightly-bench.report
DATE=`date --utc +%Y-%m-%d`

SUBJECT="Why3 ITP nightly bench:"

notify() {
    if test "$REPORTBYMAIL" == "no"; then
        cat $REPORT
    else
        mail -s "$SUBJECT" $REPORTBYMAIL < $REPORT
    fi
    exit 0
}


echo "== Why3 bench on $DATE ==" > $REPORT
echo "Starting time (UTC): "`date --utc +%H:%M` >> $REPORT

# configuration
autoconf
automake --add-missing
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

# add uninstalled prover substitution policies

COQVER=`bin/why3 --list-provers | sed -n -e 's/  Coq (\(.*\))/\1/p'`
if test "$COQVER" != "" ; then
cat >> why3.conf <<EOF

[uninstalled_prover coq85]
alternative = ""
name = "Coq"
policy = "upgrade"
target_alternative = ""
target_name = "Coq"
target_version = "$COQVER"
version = "8.5"

[uninstalled_prover coq86]
alternative = ""
name = "Coq"
policy = "upgrade"
target_alternative = ""
target_name = "Coq"
target_version = "$COQVER"
version = "8.6"

EOF
fi

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

# run regression bench for counterexamples
bench/ce-bench &> $OUT
if test "$?" != "0" ; then
    echo "Counterexample regression tests FAILED" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT (CE regression failed)"
else
    echo "Counterexample regression tests succeeded. " >> $REPORT
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

echo "Ending time (UTC): "`date --utc +%H:%M` >> $REPORT

# 3-line summary
echo "" >> $REPORT
tail -3 $OUT >> $REPORT
echo "" >> $REPORT

# output the diff against previous run
diff -u $PREVIOUS $OUT &> $DIFF
if test "$?" == 0 ; then
    echo "---------- No difference with last bench ---------- " >> $REPORT
else
    SUBJECT="$SUBJECT (with new differences)"
    if expr `cat $DIFF | wc -l` '>=' `cat $OUT | wc -l` ; then
        echo "------- Diff with last bench is larger than the bench itself ------" >> $REPORT
    else
        echo "--------------- Diff with last bench --------------" >> $REPORT
        echo "" >> $REPORT
        sed '1,2d' $DIFF >> $REPORT
    fi
    cp $OUT $PREVIOUS
fi

# finally print the full state
echo "" >> $REPORT
echo "-------------- Full current state --------------" >> $REPORT
echo "" >> $REPORT
cat $OUT >> $REPORT

# final notification after the replay
notify
