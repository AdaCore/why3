include ../../../share/Makefile.config

WHY3 = ../../../bin/why3.$(OCAMLBEST)
INCLUDE += -I ../../../lib/why3

.PHONY: extract build doc clean

build: main.opt

main.opt: clone.ml main.ml
	ocamlopt $(INCLUDE) -o $@ zarith.cmxa $^

extract: clone.ml

clone.ml: clone.mlw
	$(WHY3) extract -D ocaml64 clone.Clone -L . > $@

clean::
	rm -f clone.ml *.opt *.o *.cm*
