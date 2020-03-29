
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


BD=prover
OCAMLC=ocamlopt.opt
INCLUDES=$(INCLUDEALL) -I ../../plugins/tptp
LIBS=unix.cmxa nums.cmxa $(BIGINTLIB).cmxa dynlink.cmxa str.cmxa menhirLib.cmx zip.cmxa why3.cmxa why3extract.cmxa tptp_ast.cmx tptp_typing.cmx tptp_parser.cmx tptp_lexer.cmx
WHY3FLAGS=-L . --debug=ignore_unused_vars
MLFLAGS=
MLIFLAGS=
MLEXECFLAGS=

.PHONY: clean depend extract replay

$(BD): $(BD).cmx run.cmx
	echo "WHY3SHARE="$(WHY3SHARE)
	$(OCAMLC) $(INCLUDES) $(LIBS) $(MLFLAGS) $(MLEXECFLAGS) \
		-o $(BD) $^

extract: $(ML)

$(BD).ml:
	why3 $(WHY3FLAGS) extract -D ocaml64 -o $(BD).ml ProverTest.mlw

%.cmx: %.ml
	$(OCAMLC) $(INCLUDES) $(MLFLAGS) -c $<

.depend: Makefile $(ML)
	ocamldep.opt -I $(BD) $(ML) > .depend

ifneq "$(MAKECMDGOALS:clean%=clean)" "clean"
ifneq "$(MAKECMDGOALS:extract%=extract)" "extract"
ifneq "$(MAKECMDGOALS:extract%=replay)" "replay"
include .depend
endif
endif
endif

replay:
	@printf "===================================\n"
	@printf "Starting time (UTC): "
	@date --utc +%H:%M
	@printf "===================================\n"
	@for i in *.mlw; do \
		printf "Replaying $$i..." ; \
		why3 $(WHY3FLAGS) replay -q `basename $$i .mlw` ; \
	 done
	@printf "===================================\n"
	@printf "Ending time (UTC): "
	@date --utc +%H:%M
	@printf "===================================\n"

depend: .depend

clean:
	rm -f $(BD)/*.o $(BD)/*.cmi $(BD)/*.cmx
	rm -f $(BD)*.ml
	rm -f *~ *.o *.cmi *.cmx build/prover
