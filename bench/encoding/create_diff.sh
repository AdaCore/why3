#!/bin/bash

column=$3

bench_file1=$1
bench1=${1%.csv}
bench_file2=$2
bench2=${2%.csv}

tmpfile=$(tempfile)

reduce () {
    csvtool -t , join 1 $1 $bench_file1 $bench_file2 \
        | csvtool -t , col 2,3 - \
        | csvtool -t , drop 1 - -o $2
}

reduce $column $tmpfile

sum () {
    one=$(grep -c -E "^(3[^0]|[^3]).*,30$" $1)
    two=$(grep -c -E "^30,(3[^0]|[^3]).*$" $1)
    #none=$(grep -c -E "^30,30$" $1)
    #both=$(grep -c -E "^(3[^0]|[^3]).*,(3[^0]|[^3]).*$" $1)
    echo $one,$two
}

sum $tmpfile

rm -rf $tmpfile
#echo $tmpfile