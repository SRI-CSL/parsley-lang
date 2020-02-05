DOC=language

all: $(DOC).pdf

.PHONY: clean

TEX_SRC = $(DOC).tex parsley.bib figs/parsley-pipeline-tikz.tex

$(DOC).pdf: $(TEX_SRC) Makefile
	pdflatex $(DOC).tex
	bibtex $(DOC)
	pdflatex $(DOC).tex
	pdflatex $(DOC).tex

clean:
	rm -f $(DOC).pdf $(DOC).{aux,bbl,blg,log} figs/*.{aux,bbl,blg,log}
