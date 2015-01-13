
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
GEN=vstte12_combinators__Combinators
OBJ=$(GEN) parse

GENML = $(addsuffix .ml, $(GEN))
ML = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT=ocamlopt -noassert -inline 1000

all: $(MAIN).$(OCAMLBEST)

extract: $(GENML)

doc:
	$(WHY3) doc ../vstte12_combinators.mlw
	$(WHY3) session html .

$(MAIN).opt: $(CMX)  $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(GENML): ../vstte12_combinators.mlw
	$(WHY3) extract -D ocaml32 ../vstte12_combinators.mlw -o .

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

clean::
	rm -f $(GENML) *.cm[xio] *.o *.annot $(MAIN).opt $(MAIN).byte
	rm -f vstte12_combinators__*.ml*

# javascript


JSMAIN=jsmain

JSOCAMLC=ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax \
          -syntax camlp4o

$(JSMAIN).js: $(JSMAIN).byte
	js_of_ocaml -pretty -noinline +nat.js $(JSMAIN).byte


$(JSMAIN).byte: $(CMO) jsmain.ml
#	$(JSOCAMLC) $(INCLUDE) -o $@ -linkpkg $^
	$(JSOCAMLC) $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ -linkpkg $^


%.cmo: %.ml
	$(JSOCAMLC) $(INCLUDE) -annot -c $<

%.cmi: %.mli
	$(JSOCAMLC) $(INCLUDE) -annot -c $<


clean::
	rm -f *.cm[io] $(NAME).byte $(NAME).js
