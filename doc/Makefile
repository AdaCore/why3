HEVEA=hevea -fix

all: manual.pdf manual.html

manual.pdf: manual.tex version.tex
	pdflatex manual
	pdflatex manual

manual.html: manual.tex version.tex
	$(HEVEA) manual.tex

clean:
	rm -f $(addprefix manual, .wdvi .raux .log .aux . bbl .blg\
				  .ind .ilg .idx .html .toc)
	rm -f *.haux *.pdf *.hind *.htoc *whizzy*



.PHONY: all clean
