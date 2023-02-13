ifndef IMPORT_MAKE_ENVIRONMENT
IMPORT_MAKE_ENVIRONMENT := 1

#######
###
#   Environmental Constants
###
#######


.DEFAULT:;
SHELL := /bin/bash
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

row-delimiter := $(SPACE)\$(NEWLINE)$(SPACE)$(SPACE)$(SPACE)$(SPACE)

resource-filepath := $(abspath $(dir-slides-source)assets)/

# Thesis PDF document file path
presentation-name   := thesis-defense-presentation
presentation-latex  := $(abspath $(dir-slides-source)$(presentation-name).$(extension-latex))
presentation-target := $(abspath   $(dir-slides-deck)$(presentation-name).$(extension-portabledoc))

slides-filename := slides.md
slides-filepath := $(abspath $(dir-slides-source)$(slides-filename))

latexmk-flag-list = \
  -output-directory="$(dir $(presentation-target))"

pandoc-flag-list = \
  --columns=50 \
  --dpi=300 \
  --citeproc \
  --from=markdown \
  --listings \
  --pdf-engine=lualatex \
  --shift-heading-level=0 \
  --slide-level=2 \
  --standalone \
  --to=beamer \
  --toc \
  --variable=aspectratio:169 \
  --variable=classoption:"aspectratio=169" \
  --variable=colortheme:"orchid" \
  --variable=fontsize:11pt \
  --variable=institute:"Hunter College, CUNY" \
  --variable=lang:en-US \
  --variable=linkstyle:bold \
  --variable=section-titles:false \
  --variable=theme:"Rochester" \
  --variable=toc:true

latexmk-options := $(subst $(SPACE),$(row-delimiter),$(latexmk-flag-list))
pandoc-options  := $(subst $(SPACE),$(row-delimiter),$(pandoc-flag-list))

artifact-list := \
  $(abspath $(addprefix $(dir-slides-source)$(presentation-name).,nav snm)) \
  $(presentation-target) \
  $(presentation-latex)
artifact-rows := $(subst $(SPACE),$(row-delimiter),$(artifact-list))


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
#	( cd $(dir $(presentation-latex)); latexmk -CA; )
	-rm -f$(row-delimiter)$(artifact-rows)

#######
###
#   Build Targets
###
#######

$(dir $(presentation-target)):
	@mkdir -p $@

## Build thesis
$(dir $(presentation-latex)):
	@mkdir -p $@

$(presentation-latex): $(slides-filepath) $(dir $(presentation-latex))
	( cd $(dir-slides-source); \
	pandoc \
	  $(pandoc-options) \
	  --output=$@ \
	  $< ; \
	  sed -i'.bak' 's/<\.->/<\.->\[frame\]/g' $@; \
	)

$(presentation-target): $(presentation-latex) $(dir $(presentation-target))
	( cd $(dir $(presentation-latex)); \
	  latexmk \
	    -pdf \
	    $< ; \
	  cp \
	    $(subst $(extension-latex),$(extension-portabledoc),$(presentation-latex)) \
	    $@ ; \
	)

#$(presentation-target): $(slides-filepath) $(dir $(presentation-target))
#	( cd $(dir-slides-source); \
	pandoc \
	  $(pandoc-options) \
	  --output=$@ \
	  $< ; \
	)


endif # IMPORT_MAKE_PRESENTATION
