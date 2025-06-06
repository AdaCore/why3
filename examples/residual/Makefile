
BENCH ?= no

ifeq ($(BENCH),yes)
  WHY3=../../bin/why3.opt
  WHY3SHARE=../../share
else
  ifeq ($(BINDIR),)
    WHY3=why3
  else
    WHY3=$(BINDIR)/why3
  endif
  WHY3SHARE=$(shell $(WHY3) --print-datadir)
endif

include $(WHY3SHARE)/Makefile.config

ifeq ($(BENCH),yes)
  INCLUDE += -I ../../lib/why3
endif

MAIN=main
OBJ=residual

ML  = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT=ocamlopt -noassert -inline 1000

all: $(MAIN).$(OCAMLBEST)

extract: $(ML)

doc:
	$(WHY3) doc ../residual.mlw
	$(WHY3) session html .

$(MAIN).byte: $(CMO)  $(MAIN).cmo
	ocamlc $(INCLUDE) zarith.cma -o $@ $^

$(MAIN).opt: $(CMX)  $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) zarith.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../residual.mlw
	$(WHY3) extract -D ocaml64 -L . -L .. -D residual.drv -o $@ residual.ResidualOCaml

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

%.cmo: %.ml
	ocamlc $(INCLUDE) -annot -c $<

%.cmi: %.mli
	ocamlc $(INCLUDE) -annot -c $<

clean::
	rm -f $(ML) *.cm[xio] *.o *.annot $(MAIN).opt $(MAIN).byte
