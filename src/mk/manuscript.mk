ifndef IMPORT_MAKE_ENVIRONMENT
IMPORT_MAKE_ENVIRONMENT := 1

#######
###
#   Environmental Constants
###
#######

.ONESHELL:
.DEFAULT:;
SHELL := /bin/sh
COMMA := ,
EMPTY :=
SPACE := $(EMPTY) $(EMPTY)

endif # IMPORT_MAKE_ENVIRONMENT

ifndef IMPORT_MAKE_MANUSCRIPT
IMPORT_MAKE_MANUSCRIPT := 1

#######
###
#   Conditionl Redefinitions
###
#######

extension-figure      ?= png
extension-latex       ?= tex
extension-markdown    ?= md
extension-portabledoc ?= pdf
extension-postscript  ?= ps
dir-thesis-source     ?= ./
dir-thesis-chapters   ?= ./$(extension-markdown)/
dir-thesis-figures    ?= ./$(extension-figure)/
dir-thesis-manuscript ?= ./

#######
###
#   Custom function definitions for MANUSCRIPT
###
#######

define markdown
$(addprefix $(dir-thesis-chapters),$(addsuffix .$(extension-markdown),$(1)))
endef

define figure-output
$(call figure-with-extension,$(extension-figure),$(1))
endef

define figure-source
$(call figure-with-extension,$(extension-latex),$(1))
endef

define figure-with-extension
$(call thesis_source,$(addprefix $(dir-thesis-figures),$(addsuffix .$(1),$(2))))
endef

define thesis_source
$(abspath $(addprefix $(dir-thesis-source),$(1)))
endef

tikz-figures := $(patsubst $(call figure-source,%),$(call figure-output,%),$(wildcard $(call figure-source,*)))

#######
###
#   Variables for MANUSCRIPT
###
#######

# Title of manuscript used in file name and inside the manuscript
title-of-manuscript := Formal Verification of TreeKEM

# File format of chapters (defines ordering)
format-of-chapters  := $(addprefix chapter[0-9][0-9].,$(extension-markdown))

thesis-appendix     := $(abspath $(dir-thesis-chapters)appendix.$(extension-markdown))
thesis-backmatter   := $(call thesis_source,backmatter.tex)
thesis-bibliography := $(call thesis_source,references.bib)
thesis-chapters     := $(abspath $(sort $(wildcard $(addprefix $(dir-thesis-chapters),$(format-of-chapters)))))
thesis-frontmatter  := $(call thesis_source,frontmatter.tex)
thesis-header       := $(call thesis_source,include-header.tex)
thesis-metadata     := $(call thesis_source,metadata.yaml)
thesis-references   := $(call thesis_source,references.md)
thesis-titlepage    := $(call thesis_source,titlepage.tex)

manuscript-target   := \
    $(abspath $(dir-thesis-manuscript)$(subst $(SPACE),-,$(title-of-manuscript)).$(extension-portabledoc))

#######
###
#   Template sourcing for MANUSCRIPT
###
#######

TEMPLATE_DL_DIR      := $(call thesis_source,.tmp_template_dl)
CLEANTHESIS_TEMPLATE := cleanthesis.sty
CLEANTHESIS_REPO     := https://github.com/derric/cleanthesis
CLEANTHESIS_VERSION  := 63d1fdd815
TEMPLATE_FILES       := $(CLEANTHESIS_TEMPLATE)

#######
###
#   Auto-generated templating files for MANUSCRIPT
###
#######

TMP1 := $(thesis-titlepage:%.tex=%.filled.tex)
TMP2 := $(thesis-frontmatter:%.tex=%.filled.tex)
TMP3 := $(thesis-backmatter:%.tex=%.filled.tex)
TMP  := $(TMP1) $(TMP2) $(TMP3)

#######
###
#   Pandoc options
###
#######

AUX_OPTS       := --wrap=preserve
AUX_OPTS       += -V title:"$(title-of-manuscript)"
AUX_OPTS       += -M cleanthesis=true -M cleanthesisbibfile=$(thesis-bibliography:%.bib=%)

pandoc-options := -f markdown
pandoc-options += --pdf-engine=pdflatex
pandoc-options += --standalone
pandoc-options += -M lang=en-US
pandoc-options += --metadata-file=$(thesis-metadata)
pandoc-options += --include-in-header=$(TMP1)
pandoc-options += --include-before-body=$(TMP2)
pandoc-options += --include-after-body=$(TMP3)
pandoc-options += --citeproc
pandoc-options += -M bibliography=$(thesis-bibliography)
pandoc-options += -M link-citations=true
## download from https://www.zotero.org/styles
## cf. https://pandoc.org/MANUAL.html#citations
#pandoc-options += --csl=chicago-author-date-de.csl
#pandoc-options += --csl=chicago-note-bibliography.csl
#pandoc-options += --csl=ieee.csl
#pandoc-options += --csl=oxford-university-press-note.csl
pandoc-options += --listings
pandoc-options += -V title:"$(title-of-manuscript)"
pandoc-options += -V documentclass=scrbook
pandoc-options += -V papersize=a4
pandoc-options += -V fontsize=11pt
pandoc-options += -V classoption:open=right
pandoc-options += -V classoption:twoside=true
pandoc-options += -V classoption:cleardoublepage=empty
pandoc-options += -V classoption:clearpage=empty
pandoc-options += -V geometry:top=30mm
pandoc-options += -V geometry:left=25mm
pandoc-options += -V geometry:bottom=30mm
pandoc-options += -V geometry:width=150mm
pandoc-options += -V geometry:bindingoffset=6mm
pandoc-options += --toc
pandoc-options += --toc-depth=3
pandoc-options += --number-sections
pandoc-options += -V colorlinks=true
pandoc-options += --resource-path=$(call thesis_source,.)

#######
###
#   Standard Targets
###
#######

.PHONY: all clean distclean install installdirs pdf

all:: thesis

clean::
	@-rm -rf $(TMP) $(TEMPLATE_DL_DIR)

distclean:: clean
	@-rm -f $(manuscript-target) $(tikz-figures) $(TEMPLATE_FILES)

install:: $(manuscript-target)

installdirs:: $(dir $(manuscript-target))

#######
###
#   Phony targets
###
#######

.PHONY: thesis

## Use Clean Thesis template (https://github.com/derric/cleanthesis)
thesis: TEMPLATE_FILE    += $(CLEANTHESIS_TEMPLATE)
thesis: TEMPLATE_REPO    += $(CLEANTHESIS_REPO)
thesis: TEMPLATE_VERSION += $(CLEANTHESIS_VERSION)
#thesis: AUX_OPTS         += -M cleanthesis=true -M cleanthesisbibfile=$(thesis-bibliography:%.bib=%)
thesis: pandoc-options   += --include-in-header=$(thesis-header) $(AUX_OPTS)
thesis: $(CLEANTHESIS_TEMPLATE) $(manuscript-target)

#######
###
#   Build Targets
###
#######

$(dir $(manuscript-target)):
	@mkdir -p $@

## Download template files
$(TEMPLATE_FILES):
	@rm -rf $(TEMPLATE_DL_DIR)
	@git clone --quiet --single-branch --branch master --depth 100 $(TEMPLATE_REPO) $(TEMPLATE_DL_DIR)
	@( cd $(TEMPLATE_DL_DIR) && git checkout --quiet $(TEMPLATE_VERSION) )
	@cp $(TEMPLATE_DL_DIR)/$(TEMPLATE_FILE) ./$(TEMPLATE_FILE)
	@rm -rf $(TEMPLATE_DL_DIR)

## Build image files
$(call figure-output,%): $(call figure-source,%)
	latexmk $< -cd -output-directory=$(dir $@) -shell-escape
	latexmk $< -cd -C

## Build thesis
$(manuscript-target): $(thesis-chapters) $(thesis-references) $(APPENDIX) $(thesis-metadata) $(thesis-bibliography) $(TMP) $(tikz-figures)
	pandoc $(pandoc-options) -o $@ $(thesis-chapters) $(thesis-references) $(APPENDIX)

## Build auxiliary files (title page, frontmatter, backmatter, references)
$(TMP): $(call thesis_source,%.filled.tex: %.tex) $(thesis-metadata)
	pandoc $(AUX_OPTS) --template=$< --metadata-file=$(thesis-metadata) -o $@ $<

endif # IMPORT_MAKE_MANUSCRIPT
