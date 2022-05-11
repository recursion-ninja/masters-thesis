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

infostr-glue    := -
infostr-prefix  := CGKA

infostr :=$(subst $(SPACE),$(infostr-glue),$(infostr-prefix)\
$(protocol-version)\
$(ltl-property)\
$(foreach param,$(security-parameters),$(shell printf "$(param)%03d" $($(sec-pref)$(param)))))

infostr-pattern := $(subst $(SPACE),$(infostr-glue),$(infostr-prefix)\
$(protocol-version-pref)[0-9]\
$(ltl-property)\
$(foreach param,$(security-parameters),$(param)[0-9][0-9][0-9]))

#$(info $(NEWLINE)Unique Model Name:$(NEWLINE)$(TAB)$(infostr))

#######
###
#   Standard targets
###
#######

.PHONY: all

all::;

endif # IMPORT_MAKE_INFOSTR
