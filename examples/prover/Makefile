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


INCLUDES=$(INCLUDE) -I ../../plugins/tptp
LIBS=why3.cmxa tptp_typing.cmx tptp_parser.cmx tptp_lexer.cmx
WHY3FLAGS=-L . --warn-off=unused_variable
PKGS=$(addprefix -package ,$(EXTPKGS))

.PHONY: clean doc extract replay

main.opt: prover.cmx run.cmx
	$(OCAMLFIND) ocamlopt $(PKGS) -linkpkg $(INCLUDES) $(LIBS) -o $@ $^

extract: prover.ml

prover.ml:
	$(WHY3) $(WHY3FLAGS) extract -D ocaml64 -o prover.ml ProverTest.mlw

%.cmx: %.ml
	$(OCAMLFIND) ocamlopt $(PKGS) $(INCLUDES) -c $<

doc:

replay:
	@printf "===================================\n"
	@printf "Starting time (UTC): "
	@date --utc +%H:%M
	@printf "===================================\n"
	@for i in *.mlw; do \
		printf "Replaying $$i..." ; \
		$(WHY3) $(WHY3FLAGS) replay -q `basename $$i .mlw` ; \
	 done
	@printf "===================================\n"
	@printf "Ending time (UTC): "
	@date --utc +%H:%M
	@printf "===================================\n"

clean:
	rm -f *.o *.cmi *.cmx prover.ml main.opt
