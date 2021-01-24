include ../../share/Makefile.config

WHY3 = ../../bin/why3.$(OCAMLBEST)
INCLUDE += -I ../../lib/why3

%.ml: %.mlw
	$(WHY3) extract -D ocaml64 $< > $@

%.cmo: %.ml
	ocamlc $(INCLUDE) -c $<

%.cmx: %.ml
	ocamlopt $(INCLUDE) -c $<

%.c: %.mlw
	$(WHY3) extract -D c $< > $@

%.o: %.c
	$(CC) -Wall -c $<

clean::
	rm -f *.ml *.c *.o *.cm*
