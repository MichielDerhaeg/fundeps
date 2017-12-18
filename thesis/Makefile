MD_FILES=$(wildcard *.md)
TEX_FILES=$(wildcard *.tex) $(MD_FILES:%.md=%.tex)

.SUFFIXES: .md .tex

thesis.pdf: $(TEX_FILES)
	latexmk -pdf thesis.tex

.md.tex:
	pandoc -f markdown -t latex -o $@ $<
