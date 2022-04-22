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

ifndef IMPORT_MAKE_INFOSTR
IMPORT_MAKE_INFOSTR := 1

#######
###
#   Conditionl Redefinitions
###
#######

dir-protocol-model ?= ./
extension-makefile ?= mk

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := parameters
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables defining the "Information String"
###
#######

protocol-version-pref := v

ifndef version
protocol-version := $(protocol-version-pref)$($(def-pref)protocol-version)
else
protocol-version := $(protocol-version-pref)$(version)
endif

infostr-glue    := -
infostr-prefix  := $(subst $(SPACE),$(infostr-glue),CGKA TreeKEM)
infostr-suffix  := \
    $(subst $(SPACE),$(infostr-glue),$(protocol-version) $(foreach param,$(security-parameters),$(shell printf "$(param)%03d" $($(sec-pref)$(param)))))
infostr-suffix-pattern := \
    $(subst $(SPACE),$(infostr-glue),$(protocol-version-pref)[0-9] $(foreach param,$(security-parameters),$(param)[0-9][0-9][0-9]))

infostr         := $(infostr-prefix)$(infostr-glue)$(infostr-suffix)
infostr-pattern := $(infostr-prefix)$(infostr-glue)$(infostr-suffix-pattern)

#$(info $(NEWLINE)Unique Model Name:$(NEWLINE)$(TAB)$(infostr))

#######
###
#   Standard targets
###
#######

.PHONY: all

all::;

endif # IMPORT_MAKE_INFOSTR
