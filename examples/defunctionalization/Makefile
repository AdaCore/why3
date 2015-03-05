

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


MAIN = main
OBJ = defunctionalization__Expr \
	defunctionalization__DirectSem \
	defunctionalization__CPS \
	defunctionalization__Defunctionalization \

ML  = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT = ocamlopt -noassert -inline 1000

all: $(MAIN).opt

extract: $(ML)

doc:
	$(WHY3) doc ../defunctionalization.mlw
	$(WHY3) session html ../defunctionalization.mlw
	@echo firefox ../defunctionalization.html why3session.html

$(MAIN).byte: $(CMO) $(MAIN).cmo
	ocamlc -g $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX) $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../defunctionalization.mlw
	$(WHY3) extract -D ocaml64 ../defunctionalization.mlw -o .

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

%.cmo: %.ml
	ocamlc $(INCLUDE) -annot -g -c $<

%.cmi: %.mli
	ocamlc $(INCLUDE) -annot -g -c $<

clean::
	rm -f $(ML) *.cm[xio] $(MAIN).opt
