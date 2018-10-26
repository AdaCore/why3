ARG debian_version=stable
FROM debian:$debian_version

USER root

# install dependencies
RUN apt-get update -yq && apt-get upgrade -yq --with-new-pkgs --auto-remove
RUN apt-get update -yq && apt-get upgrade -yq --with-new-pkgs --auto-remove && apt-get install -yq --no-install-recommends wget libgmp-dev gtk+-2.0 libgtksourceview2.0-dev gnome-themes-standard libcanberra-gtk-module xvfb unzip build-essential autoconf automake ocaml-nox ca-certificates git xauth
ARG debian_packages
RUN apt-get update -yq && apt-get upgrade -yq --with-new-pkgs --auto-remove && apt-get install -yq --no-install-recommends $debian_packages
RUN apt-get clean

RUN wget https://github.com/ocaml/opam/releases/download/2.0.0/opam-2.0.0-x86_64-linux -O /usr/bin/opam && chmod 755 /usr/bin/opam

# install provers
## CVC4 1.5
RUN wget --quiet http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.5-x86_64-linux-opt
RUN chmod a+x cvc4-1.5-x86_64-linux-opt
RUN cp cvc4-1.5-x86_64-linux-opt /usr/local/bin/cvc4-1.5
## CVC4 1.4
RUN wget --quiet http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.4-x86_64-linux-opt
RUN chmod a+x cvc4-1.4-x86_64-linux-opt
RUN cp cvc4-1.4-x86_64-linux-opt /usr/local/bin/cvc4-1.4
## Z3
RUN wget --quiet https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/z3-4.6.0-x64-debian-8.10.zip
RUN unzip z3-4.6.0-x64-debian-8.10.zip
RUN cp z3-4.6.0-x64-debian-8.10/bin/z3 /usr/local/bin/z3-4.6.0

# create user
RUN adduser --disabled-password --gecos '' why3
USER why3
ENV HOME /home/why3
WORKDIR /home/why3


ARG compiler=ocaml-system
RUN opam init -a -y -j1 --compiler=$compiler --disable-sandboxing
RUN opam repository add coq-released https://coq.inria.fr/opam/released --all-switches

ARG opam_packages
RUN opam install -y depext
RUN opam depext --dry-run menhir conf-gtksourceview lablgtk ocamlgraph zarith camlzip alt-ergo
RUN opam install -y menhir conf-gtksourceview lablgtk ocamlgraph zarith camlzip alt-ergo

RUN test -z "$opam_packages" || opam depext --dry-run $opam_packages
RUN test -z "$opam_packages" || opam install -y $opam_packages
