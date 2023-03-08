
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
GEN = map__Map sudoku_reloaded__Grid sudoku_reloaded__TheClassicalSudokuGrid sudoku_reloaded__Solver
OBJ=$(GEN)

GENML = $(addsuffix .ml, $(GEN))
ML = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT = ocamlopt -noassert -inline 1000

all: $(MAIN).opt

extract: $(GENML)

doc:
	$(WHY3) doc ../sudoku_reloaded.mlw
	$(WHY3) session html .

$(MAIN).byte: $(CMO) $(MAIN).cmo
	ocamlc -g $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX) $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(GENML): ../sudoku_reloaded.mlw
	$(WHY3) extract -D ocaml32 ../sudoku_reloaded.mlw -o .

# javascript


JSMAIN=jsmain

JSOCAMLC=ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml.syntax \
          -syntax camlp4o

$(JSMAIN).js: $(JSMAIN).byte
	js_of_ocaml $(JSMAIN).byte

$(JSMAIN).byte: $(CMO) $(JSMAIN).cmo
	$(JSOCAMLC) $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ -linkpkg $^

%.cmo: %.ml
	$(JSOCAMLC) $(INCLUDE) -annot -c $<

%.cmi: %.mli
	$(JSOCAMLC) $(INCLUDE) -annot -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

clean::
	rm -f $(GENML) *.annot *.o *.cm[xio] $(MAIN).opt $(MAIN).byte
	rm -f sudoku__*.ml why3__*.ml
	rm -f int__Int.ml map__Map.ml array__Array.ml
