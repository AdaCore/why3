#!/bin/bash

# This script can be used when upgrading the prover versions in the
# bench/ce-bench and bench/check-ce-bench scripts.

# This script copies the oracle files in the folders bench/ce/oracles
# and bench/check-ce/oracles and rename the files in replacing the older
# version of a prover by a newer one.

for file in bench/ce/oracles/*_Z3,4.8.4_*.oracle; do
  cp "$file" "${file//Z3,4.8.4/Z3,4.8.10}"
done

for file in bench/check-ce/oracles/*_Z3,4.8.4_*.oracle; do
  cp "$file" "${file//Z3,4.8.4/Z3,4.8.10}"
done
