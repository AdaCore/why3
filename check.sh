# useful script for git bisect

(autoconf && ./configure --enable-local --disable-coq-libs --disable-isabelle-libs && make) || exit 125 ; bin/why3config --detect && bin/why3replay examples/linear_probing.mlw
