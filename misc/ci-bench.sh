#!/bin/bash

# runner:
# apt-get install curl opam automake libgmp-dev zlib1g-dev
# curl -L https://packages.gitlab.com/install/repositories/runner/gitlab-runner/script.deb.sh | bash
# apt-get install gitlab-runner
# gitlab-runner register
#   https://gitlab.inria.fr/
#   shell
# su gitlab-runner
# cd
# opam init
# opam install menhir alt-ergo

set -e

# configuration
autoconf
automake --add-missing 2> /dev/null || true
./configure --enable-local

# compilation
make -j2

# detection of provers
bin/why3config --detect-provers

# run the bench
make bench

# check that the realizations are ok (temporarily disabled)
# examples/regtests.sh --only-realizations
