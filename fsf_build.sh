#/bin/sh

get_abs_filename() {
  # $1 : relative filename
  echo "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
}

TARGET=$(get_abs_filename $1)
TARGETSLASH=${TARGET//\\//}

# print commands when running them
set -x
# fail on any error
set -e
opam depext zarith re seq why3
opam install dune dune-configurator menhir num ocamlgraph re seq yojson zarith sexplib ppx_sexp_conv ppx_deriving
opam exec -- ./configure --prefix=$TARGETSLASH --enable-relocation --disable-emacs-compilation --disable-hypothesis-selection --disable-js-of-ocaml --disable-zip
opam exec -- make
opam exec -- make install_spark2014
