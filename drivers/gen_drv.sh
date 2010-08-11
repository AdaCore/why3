#!/bin/sh

DIR=drivers/



replace (){
 prover=$1;
 suffix=$2;
 src=$3
 dst=$4
 cat ${DIR}${prover}.drv |sed -e "s/${src}/${dst}/" > ${DIR}${prover}_${suffix}.drv
}

for prover in z3 cvc3; do
    replace $prover "inst" transformation\ \"encoding_decorate\" transformation\ \"encoding_instantiate\"
done

for prover in z3 cvc3; do
    replace $prover "simple" transformation\ \"encoding_decorate\" \
"transformation \"encoding_enumeration\"\ntransformation \"explicit_polymorphism\"\ntransformation \"encoding_simple_kept\""
done
