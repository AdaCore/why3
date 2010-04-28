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

html:
	cd html && ./generate.sh

html_clean:
	cd html && find -name '*.html' -delete



.PHONY: all html html_clean clean
