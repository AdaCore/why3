OCAMLC=ocamlc.opt
OCAMLOPT=ocamlopt.opt
COMP=$(OCAMLOPT)
COMP=$(OCAMLC)

ROOT=../..

OPAM_LIB=$(shell opam config var lib)

PPXFLAGS=-ppx "$(OPAM_LIB)/ppx_deriving/ppx_deriving package:ppx_optcomp"

FLAGS=$(PPXFLAGS) -g

EXE=\
	mlw_tree \
	why3_prove \
	why3_ptree

INCLUDES=-I $(ROOT)/lib/why3 -I $(ROOT)/lib/why3 -I $(OPAM_LIB)/zip -I $(OPAM_LIB)/menhirLib
LIBS=\
	 menhirLib.cma \
	 str.cma \
	 unix.cma \
	 nums.cma \
	 dynlink.cma \
	 zip.cma \
	 $(ROOT)/lib/why3/why3.cma

all: clean $(EXE)

mlw_tree: mlw_tree.ml
	$(COMP) $(FLAGS) -o $@ $(INCLUDES) $(LIBS) $(ROOT)/examples/use_api/mlw_tree.ml

why3_prove: why3_prove.ml
	$(COMP) $(FLAGS) -o $@ $(INCLUDES) $(LIBS) $(ROOT)/examples/use_api/why3_prove.ml

why3_ptree: why3ml_pp.ml why3_ptree.ml
	$(COMP) $(FLAGS) -o $@ $(INCLUDES) $(LIBS) $(ROOT)/examples/use_api/why3ml_pp.ml $(ROOT)/examples/use_api/why3_ptree.ml

clean:
	rm -fv *.cm* *.o $(EXE)
