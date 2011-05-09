#!/bin/sh

echo "With Z3"
for bench in $(cat benchs); do
    echo $bench
    why3bench -B z3_$bench.rc "$@"
    echo
done

echo "With CVC3"
for bench in $(cat benchs); do
    echo $bench
    why3bench -B cvc3_$bench.rc "$@"
    echo
done

echo "With Yices"
for $bench in $(cat benchs_yices); do
    echo bench
    why3bench -B yices_$bench.rc "$@"
    echo
done