#!/bin/sh
# tests for the safe prover

timelimit=5
memlimit=1000
file=$1

report="report.txt"
reperr="report_errors.txt"

TMP=bench.out
TMPERR=bench.err

WHY3CPULIMIT=../../../lib/why3-cpulimit
$WHY3CPULIMIT $timelimit $memlimit -s build/prover $file 2> $TMPERR > $TMP
ret=$?
if test "$ret" != "0" -a "$ret" != 152 ; then
    printf "$file: ret code=$ret\n" >> $reperr
    cat $TMP >> $reperr
    cat $TMPERR >> $reperr
else
    printf "$file:\n"  >> $report
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMPERR`
    if grep "Unsat" $TMP > /dev/null ; then
        printf "Proved $time\n" >> $report
    else
        printf "Not proved $time\n" >> $report
    fi
    # zenon
    # $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s zenon-0.7.1 -p0 -itptp -max-size $memlimit"M" -max-time $timelimit"s" $file 2> $TMPERR > $TMP
    # ret=$?
    # res=`sed -n -e 's|.*(\* \(.*PROOF.*\) \*).*|\1|p' $TMP`
    # time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMPERR`
    # printf "zenon: $res $time\n" >> $report
    # eprover
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s eprover -s -R -xAuto -tAuto --cpu-limit=$timelimit --tstp-in $file 2> $TMPERR > $TMP
    ret=$?
    res=`sed -n -e 's|\(.*Proof.*\)|\1|p' $TMP`
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMPERR`
    printf "eprover: $res $time\n" >> $report
    # SPASS
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s SPASS -TPTP -PGiven=0 -PProblem=0 -TimeLimit=$timelimit $file 2> $TMPERR > $TMP
    ret=$?
    res=`sed -n -e 's|.*: \([^:]*.*Proof.*\)|\1|p' $TMP`
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMPERR`
    printf "SPASS: $res $time\n" >> $report
fi
