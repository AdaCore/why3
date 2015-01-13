
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
OBJ=vstte10_max_sum__MaxAndSum2 vstte10_max_sum__TestCase

ML  = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT=ocamlopt -noassert -inline 1000

all: $(MAIN).$(OCAMLBEST)

extract: $(ML)

doc:
	$(WHY3) doc ../vstte10_max_sum.mlw
	$(WHY3) session html .

$(MAIN).byte: $(CMO)  $(MAIN).cmo
	ocamlc $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX)  $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../vstte10_max_sum.mlw
	$(WHY3) extract -D ocaml32 ../vstte10_max_sum.mlw -o .

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

%.cmo: %.ml
	ocamlc $(INCLUDE) -annot -c $<

%.cmi: %.mli
	ocamlc $(INCLUDE) -annot -c $<

clean::
	rm -f $(ML) *.cm[xio] *.o *.annot $(MAIN).opt $(MAIN).byte
	rm -f why3__*.ml* vstte10_max_sum__*.ml* int__*.ml*



