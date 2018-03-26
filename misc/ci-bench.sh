#!/bin/bash

# Runner installation
# -------------------
# apt-get install curl
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
