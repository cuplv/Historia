######################################################################
# Makefile
#
# Makefile for LaTeX projects
######################################################################

BIBS = $(wildcard *.orig.bib)
SRCS = $(wildcard *.tex) $(wildcard *.sty) $(BIBS:%.orig.bib=%.short.bib)

SHORT_BIBS = $(BIBS:%.orig.bib=%.short.bib)

.PHONY: bib html pdf all cleandeps clean cleanall

all: pdf
pdf: ${PAPERS:%=%.pdf}
html: ${PAPERS:%=%/index.html}
bib: ${SHORT_BIBS}

${PAPERS:%=%.pdf}: ${SRCS}

cleandeps:
	rm -f ${SHORT_BIBS}
clean: cleandeps
	latexmk -c
cleanall: cleandeps
	latexmk -C
	
# Generate TR TeX
%.tr.tex: %.tex
	sed 's/\\TRfalse/\\TRtrue/' $< >$@

# Generate Posting Version TeX
%.post.tex: %.tex
	sed 's/\\Postingfalse/\\Postingtrue/' $< >$@

# Generate PDF
%.pdf: %.tex
	latexmk -pdf -use-make $<

# Detex a .tex file
%.txt: %.tex
	cat $< | detex | sed 's/---/--/g' > $@

######################################################################
# For initialization

INIT_LN = bectex.mk conference.orig.bib bec.orig.bib bec.sty mathpartir.sty
INIT_CP = Makefile
INIT_FROM = bectex

.PHONY: init initcp

# Symlink bectex files to this directory
init: $(INIT_CP)
	ln -s $(addprefix $(INIT_FROM)/, $(INIT_LN)) .

$(INIT_CP): $(INIT_CP:%=bectex/%)
	cp $(addprefix $(INIT_FROM)/, $(INIT_CP)) .
