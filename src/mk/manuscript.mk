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
dir-thesis-auxiliary  ?= $(dir-thesis-source)auxiliary/
dir-thesis-chapters   ?= $(dir-thesis-source)chapters/
dir-thesis-figures    ?= $(dir-thesis-source)figures/
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
$(addprefix $(dir-thesis-figures),$(addsuffix .$(1),$(2)))
endef

define thesis_source
$(abspath $(addprefix $(dir-thesis-source),$(1)))
endef

define thesis_auxiliary
$(abspath $(addprefix $(dir-thesis-auxiliary),$(1)))
endef

#######
###
#   Variables for MANUSCRIPT
###
#######

tikz-figures := $(patsubst $(call figure-source,%),$(call figure-output,%),$(wildcard $(call figure-source,*)))

$(info fig-source*:$(TAB) $(call figure-source,*))
$(info wildcard:$(TAB) $(wildcard $(call figure-source,*)))
$(info tikz-figures: $(tikz-figures))

row-delimiter := $(SPACE)\$(NEWLINE)$(SPACE)$(SPACE)

### Hunter Thesis template parameters:
##
# Thesis Participants
thesis-param-author      := Alex Washburn
thesis-param-advisor     := Subash Shankar
thesis-param-reader      := Sven Dietrich
thesis-param-director    := Saptarshi Debroy

# Thesis Metadata
thesis-param-title       := Formal Verification of TreeKEM
thesis-param-date        := 2022-06-20
thesis-param-year        := $(firstword $(subst -, ,$(thesis-param-date)))
thesis-param-department  := Computer Science

thesis-param-dedication  :=\
This work is dedicated to future generations, with the hope that they experiance secure communication which is intuitively usable, inveterately ubiquitous, and indelibly unrestricted.

thesis-param-acknowledge :=\
First and foremost, I would like to thank my advisor Subash Shankar for his dilligent guidance throughout my masters program. \
His numerous insights, astute inquiries, and supportive direction were paramount in completing this work. \
Similarly, I would like to thank Sven Dietrich and Saptarshi Debroy for their participation in my thesis defense and their contributions towards strengthing my final manuscript. \
Additionally I would like to thank William Sakas for his leadering as department chair, making possible the masters program under which this work was conducted. \
Finally, I want to acknowledge the support of my partner, Erilia Wu, which both remained an unwavering constant and manifested in a myriad of forms. 

thesis-param-abstract    :=\
The features of Secure Group Messaging, the security guarantees of Message Layer Security, and the TreeKEM protocol designed to satisfy these guarantees and features are explored. \
A motivation and methodology for verification via explicit model checking is presented. \
Subsequently, a translation of the TreeKEM protocol into a Promela reference model is describe, examining the nuances explicit model checking brings. \
Finally the results of the formal verifcation methods are discussed.

thesis-param-keywords    :=\
Formal Verification, Model Checking, Promela, Spin, TreeKEM

# File format of chapters (defines ordering)
format-of-chapters := $(addprefix chapter[0-9][0-9].,$(extension-latex))

# Thesis core content
thesis-chapters    := $(abspath $(sort $(wildcard $(addprefix $(dir-thesis-chapters),$(format-of-chapters)))))

# Thesis supporting contexts
thesis-preamble    := $(call thesis_auxiliary,preamble.$(extension-latex))
thesis-frontmatter := $(call thesis_auxiliary,frontmatter.$(extension-latex))
thesis-backmatter  := $(call thesis_auxiliary,backmatter.$(extension-latex))



thesis-template    := $(call thesis_source,thesis.$(extension-latex))


# Thesis references
thesis-bib-ref     := $(call thesis_auxiliary,references)
thesis-bib-path    := $(thesis-bib-ref).bib

# Thesis document class
thesis-class-ref   := $(call thesis_auxiliary,hunterthesis)
thesis-class-path  := $(thesis-class-ref).cls

# Thesis PDF document file path
manuscript-target  := \
    $(abspath $(dir-thesis-manuscript)$(subst $(SPACE),-,$(thesis-param-title)).$(extension-portabledoc))

artifact-extension :=\
    $(sort aux bcf blg dvi fdb_latexmk fls lof log out ps run.xml thm toc)
artifact-directory :=\
    $(sort $(dir-thesis-source) $(dir-thesis-auxiliary) $(dir-thesis-chapters) $(dir-thesis-figures))
artifact-filepaths :=\
    $(sort $(foreach dir,$(artifact-directory),$(addprefix $(dir)*.,$(artifact-extension))))

#######
###
#   Pandoc options
###
#######

pandoc-options := -f markdown
pandoc-options += --pdf-engine=pdflatex
pandoc-options += --standalone
#pandoc-options += --metadata-file=$(thesis-metadata)
pandoc-options += --include-in-header=$(thesis-preamble)
pandoc-options += --include-before-body=$(thesis-frontmatter)
pandoc-options += --include-after-body=$(thesis-backmatter)
pandoc-options += --resource-path=$(call thesis_source,.)
pandoc-options += --citeproc
pandoc-options += --listings
pandoc-options += --verbose

#pandoc-options += -M lang=en-US
pandoc-options += -M bibliography=$(thesis-bib-path)
pandoc-options += -M link-citations=true

## download from https://www.zotero.org/styles
#pandoc-options += --csl=ieee.csl
pandoc-options += -V thesis-var-title:"$(thesis-param-title)"
pandoc-options += -V thesis-var-author:"$(thesis-param-author)"
pandoc-options += -V thesis-var-date:"$(thesis-param-date)"
pandoc-options += -V thesis-var-year:"$(thesis-param-year)"
pandoc-options += -V thesis-var-department:"$(thesis-param-department)"
pandoc-options += -V thesis-var-advisor:"$(thesis-param-advisor)"
pandoc-options += -V thesis-var-reader:"$(thesis-param-reader)"
pandoc-options += -V thesis-var-dedication:"$(thesis-param-dedication)"
pandoc-options += -V thesis-var-acknowledge:"$(thesis-param-acknowledge)"
pandoc-options += -V thesis-var-abstract:"$(thesis-param-abstract)"
pandoc-options += -V thesis-var-keywords:"$(thesis-param-keywords)"
pandoc-options += -V documentclass=$(thesis-class-ref)
pandoc-options += -V classoption:bibfile=$(thesis-bib-ref)

#######
###
#   Standard Targets
###
#######

.PHONY: all clean distclean install installdirs pdf

all:: thesis

clean::
	-rm -f$(row-delimiter)$(manuscript-target) 
	-rm -f$(row-delimiter)$(subst $(SPACE),$(row-delimiter),$(artifact-filepaths))

distclean:: clean
	@-rm -f $(tikz-figures)

install:: $(manuscript-target)

installdirs:: $(dir $(manuscript-target))

#######
###
#   Phony targets
###
#######

.PHONY: thesis

thesis: $(HUNTERTHESIS_CLASS) $(manuscript-target)

#######
###
#   Build Targets
###
#######

$(dir $(manuscript-target)):
	@mkdir -p $@

## Build image files
$(call figure-output,%): $(call figure-source,%)
	latexmk $< -cd -output-directory=$(dir $@) -shell-escape
	latexmk $< -cd -C


## Build thesis
$(manuscript-target): $(thesis-template) $(thesis-chapters) $(thesis-bib-path) $(thesis-class-path) $(thesis-preamble) $(tikz-figures)
	( cd $(dir-thesis-source); \
	  pdflatex $<; \
	  biber    $(subst .$(extension-latex),,$<); \
	  pdflatex $<; \
	  pdflatex $<; \
	  pdflatex $<; \
	  mv $(subst $(extension-latex),$(extension-portabledoc),$<) $@; \
	)


endif # IMPORT_MAKE_MANUSCRIPT
