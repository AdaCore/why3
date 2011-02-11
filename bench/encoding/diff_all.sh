#!/bin/sh

column=$1
shift
files="$@"

echo -n $@
echo

for bench1 in $files; do
    echo -n $bench1
    for bench2 in $files; do
        res=$(./create_diff.sh $bench1 $bench2 $column)
        echo -n " $res "
    done
    echo
done
