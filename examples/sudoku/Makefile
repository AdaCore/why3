
WHY3SHARE=$(shell ../../bin/why3 --print-datadir)

include $(WHY3SHARE)/Makefile.config

MAIN = main
OBJ = sudoku__Grid sudoku__TheClassicalSudokuGrid sudoku__Solver

ML  = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))

OCAMLOPT = ocamlopt -noassert -inline 1000

all: $(MAIN).opt

extract: $(ML)

doc:
	../../bin/why3doc ../sudoku.mlw
	../../bin/why3session html ../sudoku.mlw

$(MAIN).byte: $(CMO) $(MAIN).cmo
	ocamlc -g $(INCLUDE) $(BIGINTLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX) $(MAIN).cmx
	$(OCAMLOPT) $(INCLUDE) $(BIGINTLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../sudoku.mlw
	../../bin/why3 -E ocaml32 ../sudoku.mlw -o .

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



