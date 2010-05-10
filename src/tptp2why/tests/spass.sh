#!/bin/sh

FILE=$( tempfile spass )
cat - > ${FILE} && SPASS -TPTP -PGiven=0 -PProblem=0 -TimeLimit=2 ${FILE}
rm -f ${FILE}
