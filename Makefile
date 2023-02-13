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
define NEWLINE

$(EMPTY)
endef
SPACE := $(EMPTY) $(EMPTY)
TAB   := $(shell printf '\011')

endif # IMPORT_MAKE_ENVIRONMENT

basename-encoding     := pan
basename-pbs-script   := pbs
extension-figure      := png
extension-haskell     := hs
extension-latex       := tex
extension-makefile    := mk
extension-markdown    := md
extension-promela     := pml
extension-portabledoc := pdf
extension-postscript  := ps

dir-binaries          := ./bin/
dir-data              := ./data/
dir-distribution      := ./dist/
dir-documents         := ./doc/
dir-logging           := ./log/
dir-source-code       := ./src/
dir-thesis-relative   := ./thesis/
dir-slides-relative   := ./slides/

# Source Locations
dir-make-definitions  := $(abspath $(addprefix $(dir-data),make))/
dir-pbs-script-parts  := $(abspath $(addprefix $(dir-data),$(basename-pbs-script)))/
dir-protocol-model    := $(abspath $(addprefix $(dir-source-code),model))/
dir-slides-source     := $(abspath $(dir-source-code)$(dir-slides-relative))/
dir-thesis-source     := $(abspath $(dir-source-code)$(dir-thesis-relative))/
dir-thesis-utilities  := $(abspath $(addprefix $(dir-source-code),utilities))/

# Output Locations
dir-slides-deck       := $(dir-documents)$(dir-slides-relative)
dir-thesis-manuscript := $(dir-documents)$(dir-thesis-relative)
dir-backup-record     := $(abspath $(addprefix $(dir-logging),records))/
dir-backup-trail      := $(abspath $(addprefix $(dir-logging),trails))/
dir-output-encoding   := $(dir-protocol-model)

filepath-make-definitions := $(wildcard $(dir-make-definitions)*.$(extension-makefile))

#$(info Including the following:\
  $(NEWLINE)$(TAB)$(subst $(SPACE),$(NEWLINE)$(TAB),$(notdir $(filepath-make-definitions))))

-include $(filepath-make-definitions)

all:: all-transpile


