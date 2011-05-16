#!/bin/sh

echo "Z3:"
./diff_all2.sh z3 lines columns

echo "CVC3:"
./diff_all2.sh cvc3 lines columns

echo "Yices:"
./diff_all2.sh yices yices_lines yices_columns