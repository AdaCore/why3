# useful script for git bisect

make || exit 125 ; bin/why3config --detect && bin/why3replay examples/bellman_ford.mlw
