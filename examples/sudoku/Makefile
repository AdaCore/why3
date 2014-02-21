
MAIN = main
OBJ = sudoku__Grid sudoku__TheClassicalSudokuGrid sudoku__Solver

ML  = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))


ZARITH = $(shell ocamlfind query -i-format zarith)
NUMLIB = zarith
WHY3   = -I ../../lib/why3

OCAMLOPT = ocamlopt -noassert -inline 1000

all: $(MAIN).opt

extract: $(ML)

doc:
	../../bin/why3doc ../sudoku.mlw
	../../bin/why3session html ../sudoku.mlw

$(MAIN).byte: $(CMO) $(MAIN).cmo
	ocamlc -g $(ZARITH) $(WHY3) $(NUMLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX) $(MAIN).cmx
	$(OCAMLOPT) $(ZARITH) $(WHY3) $(NUMLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../sudoku.mlw
	../../bin/why3 -E ocaml ../sudoku.mlw -o .

%.cmx: %.ml
	$(OCAMLOPT) $(WHY3) -annot -c $<

%.cmo: %.ml
	ocamlc $(WHY3) -annot -g -c $<

%.cmi: %.mli
	ocamlc $(WHY3) -annot -g -c $<

clean::
	rm -f $(ML) *.cm[xio] $(MAIN).opt $(MAIN).byte

