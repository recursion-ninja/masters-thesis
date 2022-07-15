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
dir-distribution      := ./dist/
dir-documents         := ./doc/
dir-logging           := ./log/
dir-source-code       := ./src/
dir-thesis-relative   := ./thesis/
dir-slides-relative   := ./slides/
dir-make-definitions  := $(abspath $(addprefix $(dir-source-code),$(extension-makefile)))/
dir-output-encoding   := $(abspath $(addprefix $(dir-source-code),$(basename-encoding)))/
dir-pbs-script-parts  := $(abspath $(addprefix $(dir-source-code),$(basename-pbs-script)))/
dir-protocol-model    := $(abspath $(addprefix $(dir-source-code),$(extension-promela)))/
dir-slides-source     := $(abspath $(dir-source-code)$(dir-slides-relative))/
dir-slides-deck       := $(dir-documents)$(dir-slides-relative)
dir-thesis-manuscript := $(dir-documents)$(dir-thesis-relative)
dir-thesis-source     := $(abspath $(dir-source-code)$(dir-thesis-relative))/
dir-thesis-chapters   := $(abspath $(dir-thesis-source)$(extension-markdown))/
dir-thesis-utilities  := $(abspath $(addprefix $(dir-source-code),$(extension-haskell)))/
dir-backup-record     := $(abspath $(addprefix $(dir-logging),records))/
dir-backup-trail      := $(abspath $(addprefix $(dir-logging),trails))/

filepath-make-definitions := $(wildcard $(dir-make-definitions)*.$(extension-makefile))

#$(info Including the following:\
  $(NEWLINE)$(TAB)$(subst $(SPACE),$(NEWLINE)$(TAB),$(notdir $(filepath-make-definitions))))

-include $(filepath-make-definitions)

all:: all-transpile


