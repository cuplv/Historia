######################################################################
# Makefile
#
# Makefile for LaTeX projects
######################################################################

BASE = main
PAPERS = $(BASE)

# Generate short bib
%.short.bib: %.orig.bib
	sed -e 's/@string{SHORT/@string{/' \
            -e 's/^[ 	]*[Ee]ditor/OPTeditor/' \
            -e 's/^[ 	]*[Mm]onth/OPTmonth/' \
            -e 's/^[ 	]*[Pp]ublisher/OPTpublisher/' \
            -e 's/^[ 	]*[Aa]ddress/OPTaddress/' \
            -e 's/^[ 	]*[Ii]sbn/OPTisbn/' \
            -e 's/^[ 	]*[Ii]ssn/OPTissn/' \
            -e 's/^[ 	]*[Uu]rl/OPTurl/' \
            -e 's/^[ 	]*[Dd]oi/OPTdoi/' \
            -e 's/^[ 	]*[Pp]ages/OPTpages/' \
            -e 's/^[ 	]*[Cc]rossref/OPTcrossref/' \
            -e 's/^[ 	]*[Ss]eries/OPTseries/' \
            $< > $@
						
include bectex.mk
