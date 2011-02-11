#!/bin/sh

benchs=$(echo partial_deco.csv partial_explicit.csv twin_deco.csv twin_explicit.csv)

./clean.sh $benchs
./see_result.sh $benchs
