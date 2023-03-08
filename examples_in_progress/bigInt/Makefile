
BENCH ?= no

ifeq ($(BENCH),yes)
  WHY3=../../bin/why3
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
GEN=map__Map bigInt__N
OBJ=$(GEN) parse

GENML = $(addsuffix .ml, $(GEN))
ML = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT=ocamlopt -noassert -inline 1000

all: $(MAIN).$(OCAMLBEST)

extract: $(ML)

$(MAIN).byte: $(CMO)  $(MAIN).cmo
	ocamlc $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX)  $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../bigInt.mlw
	$(WHY3) -E ocaml32 $< -o .

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

%.cmo: %.ml
	ocamlc $(INCLUDE) -annot -c $<

%.cmi: %.mli
	ocamlc $(INCLUDE) -annot -c $<

clean::
	rm -f $(GENML) *.cm[xio] *.o *.annot $(MAIN).opt $(MAIN).byte
	rm -f why3__*.ml* bigInt__*.ml* int__*.ml*


# javascript


JSMAIN=jsmain

JSOCAMLC=ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax \
          -syntax camlp4o

$(JSMAIN).js: $(JSMAIN).byte 
	js_of_ocaml -pretty -noinline $(JSMAIN).byte


$(JSMAIN).byte: $(ML) jsmain.ml
	$(JSOCAMLC) $(INCLUDE) -o $@ -linkpkg $^


%.cmo: %.ml
	$(JSOCAMLC) $(INCLUDE) -annot -c $<

%.cmi: %.mli
	$(JSOCAMLC) $(INCLUDE) -annot -c $<

