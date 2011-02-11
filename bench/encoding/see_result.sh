#!/bin/sh


#benchs=$(echo partial_deco.csv partial_deco_goal.csv partial_explicit.csv \
#    partial_explicit_goal.csv twin_deco.csv twin_explicit.csv)

benchs="$@"

echo yices
./diff_all.sh 3 $benchs
echo z3
./diff_all.sh 5 $benchs
echo cvc3
./diff_all.sh 7 $benchs