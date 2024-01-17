#!/bin/dash

set -e -x

export DEBIAN_FRONTEND=noninteractive
apt-get update -yq
apt-get upgrade -yq --with-new-pkgs --auto-remove
apt-get install -yq --no-install-recommends autoconf build-essential ca-certificates git libgmp-dev ocaml-nox opam pkg-config unzip wget zlib1g-dev
unset DEBIAN_FRONTEND

opam init -y --no-setup -j4 --bare --disable-sandboxing
opam switch create system ocaml-system
opam install -y camlzip data-encoding dolmen_loop dune-build-info dune-site js_of_ocaml-lwt js_of_ocaml-ppx lwt_ppx ocplib-simplex ppx_blob psmt2-frontend zarith_stubs_js

tar xzf trywhy3.tar.gz

git clone --branch=v2.5.2 --depth=1 https://github.com/OCamlPro/alt-ergo.git
cd alt-ergo
opam exec -- make -j4 js-worker
cp alt-ergo-worker.js ../trywhy3/
cd -
rm -rf alt-ergo

mkdir trywhy3/ace-builds trywhy3/ace-builds/src-min-noconflict/
mv trywhy3/mode-why3.js trywhy3/ace-builds/src-min-noconflict/

git clone --depth=1 https://github.com/ajaxorg/ace-builds.git
cd ace-builds/src-min-noconflict
cp ace.js mode-python.js mode-c_cpp.js theme-chrome.js ../../trywhy3/ace-builds/src-min-noconflict/
cd -
rm -rf ace-builds

tar czf trywhy3-full.tar.gz trywhy3
rm -rf trywhy3
