#!/bin/dash

column_1=2
column_2=2

bench_file1=$1
bench1=${1%.csv}
bench_file2=$2
bench2=${2%.csv}

if test "$column_1" -eq "$column_2"; then
    bench_file1_tmp=$bench_file1
    bench_file2_tmp=$bench_file2
    column=$column_1
    to_remove=""
else
    bench_file1_tmp=$(tempfile)
    csvtool -t , col 1,$column_1 $bench_file1 -o $bench_file1_tmp
    bench_file2_tmp=$(tempfile)
    csvtool -t , col 1,$column_2 $bench_file2 -o $bench_file2_tmp
    column="2"
    to_remove="$bench_file1_tmp $bench_file2_tmp"
fi

tmpfile=$(tempfile)
to_remove="$to_remove $tmpfile"

reduce () {
#    echo $column $bench_file1_tmp $bench_file2_tmp $1
    csvtool -t , join 1 $column $bench_file1_tmp $bench_file2_tmp \
        | csvtool -t , drop 1 - -o $1
}

reduce $tmpfile

sum () {
    one=$(grep -v "Valid,Valid" $1| grep -c "Valid,")
    two=$(grep -v "Valid,Valid" $1| grep -c ",Valid$")
    #none=$(grep -c -E "^30,30$" $1)
    #both=$(grep -c -E "^(3[^0]|[^3]).*,(3[^0]|[^3]).*$" $1)
    echo $one,$two
}

sum $tmpfile


if test "$3" = "show"; then
   cat $to_remove
fi

if test "$3" = "diff"; then
   cat $to_remove | grep -v "Valid,Valid"
fi

if test "$3" = "keep"; then
    echo $to_remove
else
    rm -rf $to_remove
fi
