LAGDA := $(wildcard GoI/*.lagda)
AGDAI := $(subst lagda,agdai,$(LAGDA))
TEX := $(subst lagda,tex,$(LAGDA))
STDLIB ?= /usr/share/agda-stdlib

all: report.pdf

%.tex: %.lagda
	agda --latex --latex-dir=. -i $(STDLIB) -i . $<

report.pdf: report.tex $(TEX) agda.sty
	latexmk -pdf -e '$$pdflatex=q/xelatex %O %S/' -g report.tex

clean:
	rm -rf $(AGDAI) $(TEX) auto *.aux *.fdb_latexmk *.fls *.log *.pdf *.ptb

.PHONY: clean
