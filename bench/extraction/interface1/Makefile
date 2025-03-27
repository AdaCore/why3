include ../../../share/Makefile.config

WHY3 = ../../../bin/why3.$(OCAMLBEST)

.PHONY: extract doc

main.opt: interface1.ml main.ml
	ocamlopt $(INCLUDE) zarith.cmxa $^ -o main.opt

extract: interface1.ml

doc:

%.ml: %.mlw
	$(WHY3) extract -D ocaml64 -L . --recursive interface1.Main > $@

%.cmo: %.ml
	ocamlc $(INCLUDE) -c $<

%.cmx: %.ml
	ocamlopt $(INCLUDE) -c $<

clean::
	rm -f interface1.ml main.opt *.cm*
