HEVEA=hevea -fix

all: manual.pdf manual.html

manual.pdf: manual.tex version.tex
	pdflatex manual
	pdflatex manual

manual.html: manual.tex version.tex
	$(HEVEA) manual.tex
