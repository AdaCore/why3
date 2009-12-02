 #!/bin/sh

# Note: the BINDIR variable is a free variable
# Note: the LIBDIR variable is a free variable
# Note: the COQVER variable is a free variable
# Note: the mkdirs are needed for the Ocamlbuild Makefile.

. ./Version

# Why
WHYVF=src/version.ml
mkdir -p src
echo "let coqversion = \"$COQVER\"" > $WHYVF
echo "let version = \"$VERSION\"" >> $WHYVF
echo "let date = \""`date`"\"" >> $WHYVF
echo "let bindir = \"$BINDIR\"" >> $WHYVF
echo "let libdir = \"$LIBDIR/why\"" >> $WHYVF


# Doc
DOCF=doc/version.tex
mkdir -p doc
printf '\\newcommand{\\whyversion}{'$VERSION'}\n' > $DOCF
printf '\\newcommand{\\caduceusversion}{'$CVERSION'}\n' >> $DOCF
