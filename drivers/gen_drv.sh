#!/bin/sh

DIR=drivers/

for prover in z3 cvc3; do
    for what in "" _goal _mono _def; do
        for complete in "" _nbp; do
            cat ${DIR}${prover}.drv |sed -e "s/transformation \"encoding_decorate\"/transformation \"encoding_instantiate$what$complete\"/" > ${DIR}${prover}_inst${what}${complete}.drv
        done
    done
done
