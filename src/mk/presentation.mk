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

ifndef IMPORT_MAKE_PRESENTATION
IMPORT_MAKE_PRESENTATION := 1

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
dir-slides-source     ?= ./
dir-slides-deck       ?= ./

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := manuscript
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables for PRESENTATION
###
#######

row-delimiter := $(SPACE)\$(NEWLINE)$(SPACE)$(SPACE)

# Thesis PDF document file path
presentation-name   := thesis-defense-presentation
presentation-target := $(abspath $(dir-slides-deck)$(presentation-name).$(extension-portabledoc))

slides-filename := slides.md
slides-filepath := $(abspath $(dir-slides-source)$(slides-filename))

pandoc-flag-list = \
  --columns=50 \
  --dpi=300 \
  --from=markdown \
  --listings \
  --pdf-engine=lualatex \
  --to=beamer \
  --shift-heading-level=0 \
  --slide-level=2 \
  --standalone \
  --toc \
  --metadata=author:"$(thesis-param-author)" \
  --metadata=date:"$(thesis-param-date)" \
  --metadata=title:"$(thesis-param-title)" \
  --variable=aspectratio:169 \
  --variable=classoption:"aspectratio=169" \
  --variable=colortheme:"orchid" \
  --variable=fontsize:11pt \
  --variable=institute:"Hunter College, CUNY" \
  --variable=lang:en-US \
  --variable=linkstyle:bold \
  --variable=logo:"$(abspath $(dir-slides-source)Hunter_College_logo_small.png)" \
  --variable=section-titles:false \
  --variable=theme:"Frankfurt" \
  --variable=toc:true

pandoc-options = $(subst $(SPACE),$(row-delimiter),$(pandoc-flag-list))

#######
###
#   Standard Targets
###
#######

.PHONY: all clean distclean install installdirs pdf

all:: $(presentation-target)

clean:: presentation-clean

install:: $(presentation-target)

installdirs:: $(dir $(presentation-target))

pdf:: $(presentation-target)

#######
###
#   Phony targets
###
#######

.PHONY: presentation presentation-clean

presentation: $(presentation-target)

presentation-clean:
	-rm -f$(row-delimiter)$(presentation-target)

#######
###
#   Build Targets
###
#######

$(dir $(presentation-target)):
	@mkdir -p $@

## Build thesis
$(presentation-target): $(slides-filepath) $(dir $(presentation-target))
	( cd $(dir-slides-source); \
	pandoc \
	  $(pandoc-options) \
	  --output=$@ \
	  $< ; \
	)


endif # IMPORT_MAKE_PRESENTATION
