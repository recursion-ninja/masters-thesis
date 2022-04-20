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

ifndef version
infostr-protocol-version := $($(def-pref)protocol-version)
else
infostr-protocol-version := $(version)
endif

infostr-glue            := -
infostr-model-name      := $(subst $(SPACE),$(infostr-glue),CGKA Model)
infostr-protocol-name   := $(subst $(SPACE),$(infostr-glue),TreeKEM v)
infostr-security-values := \
    $(subst $(SPACE),$(infostr-glue),$(foreach param,$(security-parameters),$($(sec-pref)$(param))))

infostr-prefix-fixed    := \
    $(subst $(SPACE),$(infostr-glue),$(infostr-model-name) $(infostr-protocol-name))
infostr-suffix-variable := \
    $(subst $(SPACE),$(infostr-glue),$(infostr-protocol-version) $(infostr-security-values))

infostr                 := $(infostr-prefix-fixed)$(infostr-suffix-variable)
infostr-pattern         := $(infostr-prefix-fixed)*

#infostr-security-keys   := \
    $(subst $(SPACE),$(infostr-glue),$(security-parameters))

#$(info ( T, C, N ) = ( '$($(sec-pref)T)', '$($(sec-pref)C)', '$($(sec-pref)N)' ))
#$(info $(infostr))

#######
###
#   Standard targets
###
#######

.PHONY: all

all::;

endif # IMPORT_MAKE_INFOSTR
