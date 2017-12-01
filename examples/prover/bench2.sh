#!/bin/sh
# tests for the safe prover

timelimit=60
memlimit=4000

report="report.txt"
reperr="report_errors.txt"
report_xml="why3session.xml"

TMP=bench.out

WHY3CPULIMIT=../../../../lib/why3-cpulimit
export TPTP=/home/marche/TPTP-v6.2.0

run_dir () {
cat << EOF > $report_xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE why3session PUBLIC "-//Why3//proof session v5//EN"
"http://why3.lri.fr/why3session.dtd">
<why3session shape_version="4">
<prover id="0" name="SafeProver" version="0.0.1" timelimit="$timelimit" memlimit="$memlimit"/>
<prover id="1" name="Zenon" version="0.8.0" timelimit="$timelimit" memlimit="$memlimit"/>
<prover id="2" name="Eprover" version="1.8" timelimit="$timelimit" memlimit="$memlimit"/>
<prover id="3" name="SPASS" version="3.7" timelimit="$timelimit" memlimit="$memlimit"/>
<prover id="4" name="Zenon_modulo" version="0.4.1" timelimit="$timelimit" memlimit="$memlimit"/>
<prover id="5" name="Vampire" version="0.6" timelimit="$timelimit" memlimit="$memlimit"/>
<prover id="6" name="LeanCoP" version="2.1" timelimit="$timelimit" memlimit="$memlimit"/>
<file name="$1.why">
<theory name="Goals">
EOF
for file in `ls $1/*.p`; do
# reprint in TPTP/FOF without include
../build/prover -print $file > $TMP 2>&1
ret=$?
if test "$ret" != "0" ; then
    printf "$file: ret code=$ret\n" >> $reperr
    cat $TMP >> $reperr
else
    printf "<goal name=\"$file\">\n" >> $report_xml
    printf "$file:\n"  >> $report
    # safeprover
    $WHY3CPULIMIT $timelimit $memlimit -s ../build/prover tmp.p > $TMP 2>&1
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMP`
    if grep "Unsat" $TMP > /dev/null ; then
        printf "<proof prover=\"0\"><result status=\"valid\" time=\"$time\"/></proof>\n" >> $report_xml
        printf "Proved $time\n" >> $report
    else
        printf "<proof prover=\"0\"><result status=\"timeout\" time=\"$time\"/></proof>\n" >> $report_xml
        printf "Not proved $time\n" >> $report
    fi
    if true ; then
    # zenon
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s zenon-0.8.0 -p0 -itptp -max-size $memlimit"M" -max-time $timelimit"s" tmp.p > $TMP 2>&1
    ret=$?
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMP`
    if grep "PROOF-FOUND" $TMP > /dev/null ; then
        printf "<proof prover=\"1\"><result status=\"valid\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Zenon error: could not find a proof within the time limit" $TMP > /dev/null ; then
        printf "<proof prover=\"1\"><result status=\"timeout\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Zenon error: could not find a proof within the memory size limit" $TMP > /dev/null ; then
        printf "<proof prover=\"1\"><result status=\"outofmemory\" time=\"$time\"/></proof>\n" >> $report_xml
    else
        printf "<proof prover=\"1\"><result status=\"unknown\" time=\"$time\"/></proof>\n" >> $report_xml
    fi
    printf "zenon: $res $time\n" >> $report
    # eprover
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s eprover -s -R -xAuto -tAuto --cpu-limit=$timelimit --tstp-in tmp.p > $TMP 2>&1
    ret=$?
    res=`sed -n -e 's|# SZS status \(.*\)|\1|p' $TMP`
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMP`
    if grep "Proof found" $TMP > /dev/null ; then
        printf "<proof prover=\"2\"><result status=\"valid\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Ran out of time\|CPU time limit exceeded" $TMP > /dev/null ; then
        printf "<proof prover=\"2\"><result status=\"timeout\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Out of Memory" $TMP > /dev/null ; then
        printf "<proof prover=\"2\"><result status=\"outofmemory\" time=\"$time\"/></proof>\n" >> $report_xml
    else
        printf "<proof prover=\"2\"><result status=\"unknown\" time=\"$time\"/></proof>\n" >> $report_xml
    fi
    printf "eprover: $res $time\n" >> $report
    # SPASS
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s SPASS -TPTP -PGiven=0 -PProblem=0 -TimeLimit=$timelimit tmp.p > $TMP 2>&1
    ret=$?
    res=`sed -n -e 's|SPASS beiseite: \(.*\)|\1|p' $TMP`
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMP`
    if grep "Proof found" $TMP > /dev/null ; then
        printf "<proof prover=\"3\"><result status=\"valid\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Ran out of time\|CPU time limit exceeded" $TMP > /dev/null ; then
        printf "<proof prover=\"3\"><result status=\"timeout\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Out of Memory" $TMP > /dev/null ; then
        printf "<proof prover=\"3\"><result status=\"outofmemory\" time=\"$time\"/></proof>\n" >> $report_xml
    else
        printf "<proof prover=\"3\"><result status=\"unknown\" time=\"$time\"/></proof>\n" >> $report_xml
    fi
    printf "SPASS: $res $time\n" >> $report
    # zenon modulo
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s zenon_modulo -p0 -itptp -max-size $memlimit"M" -max-time $timelimit"s" tmp.p > $TMP 2>&1
    ret=$?
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMP`
    if grep "PROOF-FOUND" $TMP > /dev/null ; then
        printf "<proof prover=\"4\"><result status=\"valid\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Zenon error: could not find a proof within the time limit" $TMP > /dev/null ; then
        printf "<proof prover=\"4\"><result status=\"timeout\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Zenon error: could not find a proof within the memory size limit" $TMP > /dev/null ; then
        printf "<proof prover=\"4\"><result status=\"outofmemory\" time=\"$time\"/></proof>\n" >> $report_xml
    else
        printf "<proof prover=\"4\"><result status=\"unknown\" time=\"$time\"/></proof>\n" >> $report_xml
    fi
    printf "zenon_modulo: $res $time\n" >> $report
    # Vampire
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s vampire -t $timelimit"s" < tmp.p > $TMP 2>&1
    ret=$?
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMP`
    if grep "Refutation found" $TMP > /dev/null ; then
        printf "<proof prover=\"5\"><result status=\"valid\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Time limit reached\|Time out" $TMP > /dev/null ; then
        printf "<proof prover=\"5\"><result status=\"timeout\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Memory limit exceeded" $TMP > /dev/null ; then
        printf "<proof prover=\"5\"><result status=\"outofmemory\" time=\"$time\"/></proof>\n" >> $report_xml
    else
        printf "<proof prover=\"5\"><result status=\"unknown\" time=\"$time\"/></proof>\n" >> $report_xml
    fi
    printf "vampire: $res $time\n" >> $report
    # LeanCoP
    $WHY3CPULIMIT `expr $timelimit + 1` $memlimit -s /home/marche/Downloads/leancop21/leancop.sh tmp.p $timelimit > $TMP 2>&1
    ret=$?
    time=`sed -n -e 's|.*time : \(.*\) s.*|\1|p' $TMP`
    if grep "is a Theorem\|is a Non-Theorem\|is Unsatisfiable" $TMP > /dev/null ; then
        printf "<proof prover=\"6\"><result status=\"valid\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Timeout\|Time out" $TMP > /dev/null ; then
        printf "<proof prover=\"6\"><result status=\"timeout\" time=\"$time\"/></proof>\n" >> $report_xml
    elif grep "Memory limit exceeded" $TMP > /dev/null ; then
        printf "<proof prover=\"6\"><result status=\"outofmemory\" time=\"$time\"/></proof>\n" >> $report_xml
    else
        printf "<proof prover=\"6\"><result status=\"unknown\" time=\"$time\"/></proof>\n" >> $report_xml
    fi
    printf "leancop: $res $time\n" >> $report
    # end of proofs
    fi
    printf "</goal>\n" >> $report_xml
fi
done
cat << EOF >> $report_xml
</theory>
</file>
</why3session>
EOF
}


run_dir $1
