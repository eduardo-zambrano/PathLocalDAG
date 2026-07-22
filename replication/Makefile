.PHONY: all table1 figure

all: table1 figure

table1:
	Rscript table1_enumeration.R

figure:
	pdflatex -interaction=nonstopmode -halt-on-error figure_pathlocal.tex
