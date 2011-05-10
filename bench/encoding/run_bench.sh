#!/bin/sh

WHY3BENCH="../../bin/why3bench -C why.conf"

echo "With Z3"
for bench in $(cat benchs); do
    echo $bench
    $WHY3BENCH -B z3_$bench.rc $ARGS
    echo
done

echo "With CVC3"
for bench in $(cat benchs); do
    echo $bench
    $WHY3BENCH -B cvc3_$bench.rc $ARGS
    echo
done

echo "With Yices"
for bench in $(cat benchs_yices); do
    echo $bench
    $WHY3BENCH -B yices_$bench.rc
    echo
done