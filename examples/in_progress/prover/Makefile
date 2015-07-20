
BENCH ?= no

ifeq ($(BENCH),yes)
  WHY3=../../../bin/why3.opt
  WHY3SHARE=../../../share
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


MLW=BacktrackArray Firstorder_symbol_impl ISet Firstorder_term_impl \
	Firstorder_formula_impl Firstorder_formula_list_impl \
	Firstorder_tableau_impl Unification FormulaTransformations \
	Prover ProverMain ProverTest

BD=build
MLUTIL=$(BD)/Nat__Nat
MLTYPES=$(patsubst %,$(BD)/%__Types,$(MLW))
MLIMPL=$(patsubst %,$(BD)/%__Impl,$(MLW))
ML=$(MLUTIL) $(MLTYPES) $(MLIMPL)
CMX=$(patsubst %,%.cmx,$(ML))
CMI=$(patsubst %,%.cmi,$(ML))
OCAMLC=ocamlopt.opt
INCLUDES=-I $(BD) $(INCLUDE)
LIBS=nums.cmxa why3__BuiltIn.cmx int__Int.cmx array__Array.cmx
WHY3FLAGS=-L . --debug ignore_unused_vars
MLFLAGS=
MLIFLAGS=
MLEXECFLAGS=

$(BD)/prover: $(CMX) $(BD)/Prover.ml
	echo $(OCAMLC) $(INCLUDES) $(LIBS) $(MLFLAGS) $(MLEXECFLAGS) \
		-o $(BD)/prover $<

%.cmx: %.ml
	$(OCAMLC) $(INCLUDES) $(MLFLAGS) -c $<

$(BD)/Nat__Nat.ml: Nat.mlw
	why3 $(WHY3FLAGS) extract -D ocaml64 -o $(BD) $< -T Nat

$(BD)/%__Types.ml: %.mlw
	why3 $(WHY3FLAGS) extract -D ocaml64 -o $(BD) $< -T Types

$(BD)/%__Impl.ml: %.mlw
	why3 $(WHY3FLAGS) extract -D ocaml64 -o $(BD) $< -T Impl


.PHONY: clean depend .depend

depend: .depend

.depend: Makefile $(patsubst %,%.ml,$(ML))
	ocamldep.opt -I $(BD) $(patsubst %,%.ml,$(ML)) > .depend

ifneq "$(MAKECMDGOALS:clean%=clean)" "clean"
include .depend
endif

clean:
	rm -f $(BD)/*.o $(BD)/*.cmi $(BD)/*.cmx
	rm -f $(BD)/*__*.ml
