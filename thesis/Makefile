
export TEXINPUTS := .:./Styles//:${TEXINPUTS}
export BSTINPUTS := .:./Styles//:${BSTINPUTS}
export SHELL := /bin/bash

MD_FILES=
TEX_FILES=$(wildcard *.tex) $(MD_FILES:%.md=%.tex)

.SUFFIXES: .md .tex

thesis.pdf: $(TEX_FILES)
	latexmk -pdf thesis.tex

.md.tex:
	pandoc -f markdown -t latex -o $@ $<


clean:
	$(RM) *.dvi *.aux *.log *.bbl *.blg *.toc *.out *.fls *.haux *.ptb *.fdb_latexmk *~

distclean: clean
	$(RM) thesis.pdf

