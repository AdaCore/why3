
BENCH ?= no

ifeq ($(BENCH),yes)
  WHY3=../../bin/why3
  WHY3SHARE=../../share
else
  WHY3=$(BINDIR)/why3
  WHY3SHARE=$(shell $(WHY3) --print-datadir)
endif

include $(WHY3SHARE)/Makefile.config

ifeq ($(BENCH),yes)
  INCLUDE += -I ../../lib/why3
endif

MAIN = main
OBJ = map__Map sudoku__Grid sudoku__TheClassicalSudokuGrid sudoku__Solver

ML  = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT = ocamlopt -noassert -inline 1000

all: $(MAIN).opt

extract: $(ML)

doc:
	$(WHY3)doc ../sudoku.mlw
	$(WHY3)session html ../sudoku.mlw

$(MAIN).byte: $(CMO) $(MAIN).cmo
	ocamlc -g $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX) $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../sudoku.mlw
	$(WHY3)extract -D ocaml32 ../sudoku.mlw -o .

%.cmx: %.ml
	$(OCAMLOPT) $(INCLUDE) -annot -c $<

%.cmo: %.ml
	ocamlc $(INCLUDE) -annot -g -c $<

%.cmi: %.mli
	ocamlc $(INCLUDE) -annot -g -c $<

clean::
	rm -f $(ML) *.annot *.o *.cm[xio] $(MAIN).opt $(MAIN).byte
	rm -f sudoku__*.ml why3__*.ml
	rm -f int__Int.ml map__Map.ml array__Array.ml



