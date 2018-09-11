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

while test $# -gt 0
do
    case "$1" in
        bench)
            bin/why3config --detect-provers
            make bench
            ;;
        ide)
            WHY3CONFIG="" xvfb-run bin/why3 ide --batch "" examples/logic/einstein.why
            ;;
        doc)
            make doc
            ;;
        ce-bench)
            bin/why3config --detect-provers
            bench/ce-bench
            ;;
        nightly-bench-reduced)
            bin/why3config --detect-provers
            sed -i why3.conf -e "s/running_provers_max = [0-9]*/running_provers_max = 1/"
            cat misc/bench-few-provers-why3-conf >> why3.conf
            examples/regtests.sh --reduced-mode
            ;;
    esac
    shift
done
