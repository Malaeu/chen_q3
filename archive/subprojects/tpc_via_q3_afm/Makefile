# Makefile for TPC via Q3+AFM paper

MAIN = main
TEX = pdflatex
BIB = bibtex

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex sections/*/*.tex
	$(TEX) $(MAIN)
	$(BIB) $(MAIN) || true
	$(TEX) $(MAIN)
	$(TEX) $(MAIN)

clean:
	rm -f *.aux *.log *.bbl *.blg *.out *.toc *.lof *.lot

distclean: clean
	rm -f $(MAIN).pdf

.PHONY: all clean distclean
