#!/bin/bash

# Runner installation
# -------------------
# apt-get update
# apt-get install curl autoconf automake
# curl -L https://packages.gitlab.com/install/repositories/runner/gitlab-runner/script.deb.sh | bash
# curl -fsSL https://download.docker.com/linux/debian/gpg | apt-key add -
# apt-key fingerprint 0EBFCD88
# echo "deb https://download.docker.com/linux/debian stretch stable" >> /etc/apt/sources.list
# apt-get update
# apt-get install gitlab-runner docker-ce
# gitlab-runner register
#   https://gitlab.inria.fr/
#   shell
# usermod -aG docker gitlab-runner

set -e
eval `opam config env`

./configure --enable-local
make

if test "$1" = bench; then
bin/why3config --detect-provers
make bench
fi
