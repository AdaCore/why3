
MAIN = main
OBJ = defunctionalization__Expr \
	defunctionalization__DirectSem \
	defunctionalization__CPS \
	defunctionalization__Defunctionalization \

ML  = $(addsuffix .ml, $(OBJ))
CMO = $(addsuffix .cmo, $(OBJ))
CMX = $(addsuffix .cmx, $(OBJ))


ZARITH = $(shell ocamlfind query -i-format zarith)
NUMLIB = zarith
WHY3   = $(shell ocamlfind query -i-format why3)

OCAMLOPT = ocamlopt -noassert -inline 1000

all: $(MAIN).opt

doc:
	why3doc ../defunctionalization.mlw
	why3session html ../defunctionalization.mlw
	firefox defunctionalization.mlw.html defunctionalization.html &

$(MAIN).byte: $(CMO) $(MAIN).cmo
	ocamlc -g $(ZARITH) $(WHY3) $(NUMLIB).cma why3extract.cma -o $@ $^

$(MAIN).opt: $(CMX) $(MAIN).cmx
	$(OCAMLOPT) $(ZARITH) $(WHY3) $(NUMLIB).cmxa why3extract.cmxa -o $@ $^

$(MAIN).cmx: $(CMX)

$(ML): ../defunctionalization.mlw
	why3 -E ocaml ../defunctionalization.mlw -o .

%.cmx: %.ml
	$(OCAMLOPT) $(WHY3) -annot -c $<

%.cmo: %.ml
	ocamlc $(WHY3) -annot -g -c $<

%.cmi: %.mli
	ocamlc $(WHY3) -annot -g -c $<

clean::
	rm -f $(ML) *.cm[xio] $(MAIN).opt

