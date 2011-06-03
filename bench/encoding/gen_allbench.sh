#!/bin/dash

PROVER="z3 cvc3 yices"
SELECT_INST="none goal all"
SELECT_LSKEPT="none goal all"
SELECT_LSINST="none goal all"
SELECT_KEPT="none goal all"
ENCO_KEPT="twin partial"
ENCO_POLY="deco explicit guard"

dirname=$(dirname $0)

for P in $PROVER; do
for SI in $SELECT_INST; do
for SLK in $SELECT_LSKEPT; do
for SLI in $SELECT_LSINST; do
for SK in $SELECT_KEPT; do
for EK in $ENCO_KEPT; do
for EP in $ENCO_POLY; do
$dirname/create_bench.sh $P $SI $SLK $SLI $SK $EK $EP
done done done done done done done
