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

GITBRANCH=`git rev-parse --abbrev-ref HEAD`
REPORTDIR=$PWD/../why3-reports-$GITBRANCH

OUT=$REPORTDIR/nightly-bench.out
PREVIOUS=$REPORTDIR/nightly-bench.previous
DIFF=$REPORTDIR/nightly-bench.diff
REPORT=$REPORTDIR/nightly-bench.report

if ! test -e "$REPORTDIR"; then
    echo "directory '$REPORTDIR' for reports does not exist, creating."
    mkdir "$REPORTDIR"
    touch "$PREVIOUS"
fi

LASTCOMMIT=$REPORTDIR/lastcommit

DATE=`date --utc +%Y-%m-%d`
SUBJECT="Why3 [$GITBRANCH] bench : "

notify() {
    if test "$REPORTBYMAIL" == "no"; then
        cat $REPORT
    else
        mail -s "$SUBJECT" $REPORTBYMAIL < $REPORT
    fi
    exit 0
}

LASTCOMMITHASH=$(cat $LASTCOMMIT 2>/dev/null || echo 'none')
NEWCOMMITHASH=$(git rev-parse HEAD)

if test $LASTCOMMITHASH = $NEWCOMMITHASH; then
    echo "Not running nightly bench: last commit is the same as for previous run" > $REPORT
    SUBJECT="$SUBJECT not run (no new commit)"
else
echo "== Why3 bench on $DATE ==" > $REPORT
echo "Starting time (UTC): "`date --utc +%H:%M` >> $REPORT
echo "Current branch: "$GITBRANCH >> $REPORT
echo "Current commit: "$NEWCOMMITHASH >> $REPORT

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

COQVER=$(bin/why3 --list-provers | sed -n -e 's/  Coq (\?\([0-9.]\+\).*/\1/p')
echo "Coq version detected: $COQVER" >> $REPORT
if test "$COQVER" != "" ; then
sed bench-coq-why3-conf -e "s/@COQVER@/$COQVER/g"  >> why3.conf
fi

# run the bench
make bench &> $OUT
if test "$?" != "0" ; then
    echo "Make bench FAILED" >> $REPORT
    tail -20 $OUT >> $REPORT
    SUBJECT="$SUBJECT make bench failed,"
    # we do not notify yet, we try the examples also
    # notify
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
    echo "REPLAY SUCCEEDED" >> $REPORT
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

echo $NEWCOMMITHASH > $LASTCOMMIT

fi # end of test if LASTCOMMITHASH = NEWCOMMITHASH

# final notification after the replay
notify
