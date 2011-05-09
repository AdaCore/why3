#!/bin/dash

prover="$1"
lines="$2"
columns="$3"

for column in $(cat $columns); do
    echo -n " $column"
done
echo

for line in $(cat $lines); do
    echo -n $line
    for column in $(cat $columns); do
        res=$(./create_diff.sh ${prover}_${line}.csv ${prover}_${column}.csv 2 2)
        echo -n " $res"
    done
    echo
done
