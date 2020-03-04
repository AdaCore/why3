# Standalone file that can be used in a slim environment that is insufficient
# for passing configure (e.g., for continuous integration).
# It is included by the main Makefile.

doc/generated/drivers-all.dot: drivers/*.drv drivers/*.gen
	doc/drv_depgraph $^ > $@

doc/generated/drivers-%.dot: doc/generated/drivers-all.dot
	ccomps -X $(NODE) $< > $@

doc/generated/drivers-smt.dot: NODE = smt-libv2.gen
doc/generated/drivers-tptp.dot: NODE = tptp.gen
doc/generated/drivers-coq.dot: NODE = coq-common.gen
doc/generated/drivers-isabelle.dot: NODE = isabelle-common.gen
doc/generated/drivers-pvs.dot: NODE = pvs-common.gen

DRVDOT = $(patsubst %,doc/generated/drivers-%.dot, smt tptp coq isabelle pvs)

DOC = index zebibliography genindex \
  foreword starting whyml api install manpages syntaxref input_formats exec itp technical changes

DOCRST = $(DOC:%=doc/%.rst)

public/index.html: $(DOCRST) $(DRVDOT)
	sphinx-build -W --keep-going -b html doc public
