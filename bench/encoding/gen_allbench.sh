#!/bin/dash

PROVER="z3 cvc3 yices"
SELECT_INST="nothing goal context"
SELECT_KEPT="nothing goal context"
SELECT_LSKEPT="nothing goal context"
PRODUCT_MODE="nothing only_kept some_kept"
ENCO_KEPT="twin partial"
ENCO_POLY="deco explicit guard"

dirname=$(dirname $0)

for P in $PROVER; do
for SI in $SELECT_INST; do
for SK in $SELECT_KEPT; do
for SL in $SELECT_LSKEPT; do
for PM in $PRODUCT_MODE; do
for EK in $ENCO_KEPT; do
for EP in $ENCO_POLY; do
$dirname/create_bench.sh $P $SI $SK $SL $PM $EK $EP
done done done done done done done