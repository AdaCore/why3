include ../../../share/Makefile.config

WHY3 = ../../../bin/why3.$(OCAMLBEST)

.PHONY: extract doc

main.opt: test.ml main.ml
	ocamlopt $(INCLUDE) zarith.cmxa $^ -o main.opt

extract: test.ml

doc:

%.ml: ../%.mlw
	$(WHY3) extract -D ocaml64 $< > $@

%.cmo: %.ml
	ocamlc $(INCLUDE) -c $<

%.cmx: %.ml
	ocamlopt $(INCLUDE) -c $<

clean::
	rm -f test.ml main.opt *.cm*
