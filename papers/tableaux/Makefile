# $Id$

PDFLATEX=pdflatex
BIBTEX=bibtex
TEX=archsat.tex
PDF=$(TEX:.tex=.pdf)

all: $(PDF)

check:
	make -s clean; make -s all &> /dev/null; \
        echo "$(PDFLATEX):"; $(PDFLATEX) $(TEX) | \
        grep "Overfull \\\hbox\|undefined on"; echo "$(BIBTEX):"; \
        $(BIBTEX) $(TEX:.tex=) | grep "Error\|Warning"; exit 0

clean:
	rm -f *~ .*~ *.aux *.bbl *.blg *.log *.pdf

$(PDF): $(TEX) $(wildcard *.tex) $(wildcard *.bib)
	$(PDFLATEX) $<; $(BIBTEX) $(<:.tex=); \
        for i in `seq 2`; do $(PDFLATEX) $<; done
