#!/bin/dash

PROVER=$1
SELECT_INST=Inst_$2
SELECT_LSKEPT=Lskept_$3
SELECT_LSINST=Lsinst_$4
SELECT_KEPT=Kept_$5
ENCO_KEPT=Kept_$6
ENCO_POLY=Poly_$7

BENCH_NAME="${PROVER}_${SELECT_INST}_${SELECT_LSKEPT}_${SELECT_LSINST}_${SELECT_KEPT}_${ENCO_KEPT}_${ENCO_POLY}"

FILE=${BENCH_NAME}.rc

echo "bench written to $FILE"
sed template_rc \
    -e "s/@BENCH_NAME@/$BENCH_NAME/" \
    -e "s/@PROVER@/$PROVER/" \
    -e "s/@SELECT_INST@/$SELECT_INST/" \
    -e "s/@SELECT_LSKEPT@/$SELECT_LSKEPT/" \
    -e "s/@SELECT_LSINST@/$SELECT_LSINST/" \
    -e "s/@SELECT_KEPT@/$SELECT_KEPT/" \
    -e "s/@ENCO_KEPT@/$ENCO_KEPT/" \
    -e "s/@ENCO_POLY@/$ENCO_POLY/" \
    > $FILE

# TMPFILE=/tmp/create_bench_log.file *)
# echo -n "test: " *)
# why3-cpulimit 1 0 -h why3bench -B $FILE > $TMPFILE 2>&1 *)
# case $? in *)
#     152) *)
#         echo "Ok" *)
#         ;; *)
#     1) *)
#         cat $TMPFILE *)
#         exit 1 *)
#         ;; *)
#     *\) *)
#         echo "Unknown error"; *)
#         exit 2 *)
# esac *)
