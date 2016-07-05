
BINDIR=/usr/local/bin

OCAMLFIND = ocamlfind

OCAMLFIND_OPT = $(addprefix -package ,$(PACKAGES)) -annot
OCAMLOPT = $(OCAMLFIND) ocamlopt $(OCAMLFIND_OPT)
OCAMLC = $(OCAMLFIND) ocamlc $(OCAMLFIND_OPT)
OCAMLDEP = $(OCAMLFIND) ocamldep $(OCAMLFIND_OPT)

PACKAGES = unix str

all:makejob runstrat
opt: makejob.opt runstrat.opt
byte: makejob.byte runstrat.byte

printconf:
	echo $(OCAMLPATH)
	ocamlfind printconf

makeproto.cmo: makeproto.cmi
makeproto.cmx: makeproto.cmi

makejob.opt: makeproto.cmx makejob.ml
makejob.byte: makeproto.cmo makejob.ml

makejob: makejob.opt
	@rm -f makejob
	ln -s makejob.opt makejob

runstrat.opt runstrat.byte: PACKAGES += why3
runstrat.opt: makeproto.cmx runstrat.ml
runstrat.byte: makeproto.cmo runstrat.ml

runstrat: runstrat.opt
	@rm -f runstrat
	ln -s runstrat.opt runstrat

install:
	mkdir -p $(BINDIR)
	cp runstrat.opt $(BINDIR)/runstrat
	cp makejob.opt $(BINDIR)/makejob

clean:
	rm -f *.cmo *.cma *.cmx *.cmi *.o *.annot *.opt
	rm -f runstrat makejob

### Tests ###

.PHONY: test_makejob %.test_makejob_aux

TEST_MAKEJOB=$(addsuffix .test_makejob_aux , $(shell seq 5 -1 1))

test_makejob: $(TEST_MAKEJOB)
	@echo Done $(TEST_MAKEJOB)

%.test_makejob_aux: makejob
	@echo Run $*
	+./run_wait.ml e 10 ./echo_wait.ml $*
	@echo Done $*


################
# generic rules
################

%.cmi: %.mli
	$(SHOW) 'Ocamlc   $<'
	$(HIDE)$(OCAMLC) -c $<

%.cmo: %.ml
	$(SHOW) 'Ocamlc   $<'
	$(HIDE)$(OCAMLC) -c $<

%.cmx: %.ml
	$(SHOW) 'Ocamlopt $<'
	$(HIDE)$(OCAMLOPT) -c $<

%.dep: %.ml
	$(SHOW) 'Ocamldep $<'
	$(HIDE)$(OCAMLDEP) $(DEPFLAGS) $< $<i $(TOTARGET)

%.opt:
	$(SHOW) 'Ocamlopt $<'
	$(HIDE)$(OCAMLOPT) -linkpkg -o $@ $^

%.byte:
	$(SHOW) 'Ocamlc   $<'
	$(HIDE)$(OCAMLC) -linkpkg -o $@ $^
