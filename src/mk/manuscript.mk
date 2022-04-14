ifndef IMPORT_MAKE_ENVIRONMENT
IMPORT_MAKE_ENVIRONMENT ::= 1

#######
###
#   Environmental Constants
###
#######

.ONESHELL:
.DEFAULT:;
SHELL ::= /bin/sh
COMMA ::= ,
EMPTY ::=
SPACE ::= $(EMPTY) $(EMPTY)

endif # IMPORT_MAKE_ENVIRONMENT

ifndef IMPORT_MAKE_MANUSCRIPT
IMPORT_MAKE_MANUSCRIPT ::= 1

#######
###
#   Conditionl Redefinitions
###
#######

extension-markdown    ?= md
extension-portabledoc ?= pdf
dir-thesis-chapters   ?= ./
dir-thesis-manuscript ?= ./

#######
###
#   Variables for MANUSCRIPT
###
#######

# Input `pandoc` variables for manuscript compilation
filename-schema     ::= schema
filepath-schema     ::= $(abspath $(addprefix $(dir-thesis-chapters),$(addsuffix .$(extension-markdown),$(filename-schema))))
# Input content of manuscript
formatof-chapters   ::= $(addprefix chapter[0-9][0-9].,$(extension-markdown))
filepath-chapters   ::= $(abspath $(sort $(wildcard $(addprefix $(dir-thesis-chapters),$(formatof-chapters)))))
# Title of manuscript used in file name and inside the manuscript
title-of-manuscript ::= Formal Verification of TreeKEM
# Output of manuscript
filename-manuscript ::= $(subst $(SPACE),-,$(title-of-manuscript)).$(extension-portabledoc)
filepath-manuscript ::= $(abspath $(dir-thesis-manuscript)$(filename-manuscript))
# Temporary files created during manuscript compilation
artifact-manuscript ::= bbl blg synctex.gz toc

#######
###
#   Phony Targets
###
#######

.PHONY: all-manuscript clean-manuscript install-manuscript installdirs-manuscript pdf-manuscript

all-manuscript: install-manuscript

clean-manuscript:
	-rm -f $(filepath-manuscript)
	@$(eval artifact-manuscript-found ::= $(wildcard $(addprefix *.,$(artifact-manuscript))))
	@$(if $(strip $(artifact-manuscript-found)),rm -f $(artifact-manuscript-found),)

install-manuscript: installdirs-manuscript $(filepath-manuscript)

installdirs-manuscript: $(dir $(filepath-manuscript))

pdf-manuscript: install-manuscript

#######
###
#   Build Targets
###
#######

$(dir $(filepath-manuscript)):
	@mkdir -p $@

$(filepath-manuscript): $(filepath-schema) $(filepath-chapters)
	@pandoc --table-of-contents \
	-V title:"$(title-of-manuscript)" \
	-o $@ $^
	@$(eval location-of-manuscript:=$(shell realpath --relative-to=. $@))
	@echo "Manuscript created at location:\n\t$(location-of-manuscript)"

endif # IMPORT_MAKE_MANUSCRIPT
