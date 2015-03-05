
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
GEN=map__Map mach__int__UInt32 mp__N
OBJ=$(GEN) parse

GENML = $(addsuffix .ml, $(GEN))
ML = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT=ocamlopt -noassert -inline 1000

all: $(MAIN).$(OCAMLBEST)

extract: $(GENML)

parse.cmo: mp__N.cmo


$(MAIN).byte: $(CMO)  $(MAIN).cmo
	ocamlc $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -g -o $@ $^

$(MAIN).opt: $(CMX)  $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(GENML): ../mp.mlw
	$(WHY3) extract -D ocaml32 $< -o .

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

%.cmo: %.ml
	ocamlc -g $(INCLUDE) -annot -c $<

%.cmi: %.mli
	ocamlc -g $(INCLUDE) -annot -c $<

clean::
	rm -f $(GENML) *.cm[xio] *.o *.annot $(MAIN).opt $(MAIN).byte
	rm -f why3__*.ml* mp__*.ml* int__*.ml*


# javascript


JSMAIN=jsmain

JSOCAMLC=ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax \
          -syntax camlp4o

$(JSMAIN).js: $(JSMAIN).byte
	js_of_ocaml +nat.js $(JSMAIN).byte


$(JSMAIN).byte: $(CMO) jsmain.ml
	$(JSOCAMLC) $(INCLUDE) -o $@ -linkpkg nums.cma why3extract.cma $^


%.cmo: %.ml
	$(JSOCAMLC) $(INCLUDE) -g -annot -c $<

%.cmi: %.mli
	$(JSOCAMLC) $(INCLUDE) -g -annot -c $<

