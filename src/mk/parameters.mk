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

ifndef IMPORT_MAKE_PARAMETERS
IMPORT_MAKE_PARAMETERS := 1

#######
###
#   Conditionl Redefinitions
###
#######

dir-protocol-model ?= ./
extension-promela  ?= pml

#######
###
#   Variables for CONSTANTS
###
#######

def-pref := default-
sec-pref := security-parameter-

$(def-pref)protocol-version := 1
$(def-pref)$(sec-pref)T     := 12
$(def-pref)$(sec-pref)C     := 12
$(def-pref)$(sec-pref)N     := 8

basename-constants := Parameterized-Constants
filename-constants := $(addsuffix .$(extension-promela),$(basename-constants))
filepath-constants := $(abspath $(addprefix $(dir-protocol-model),$(filename-constants)))

#######
###
#   Custom function definitions for PARAMETERS
###
#######

define security_parameter
$(if $(strip $($(1))),$($(1)),$(if $(strip $(wildcard $(filepath-constants))),$(shell sed -n 's/^#define \+$(1) \+\([^ ]\+\) *$$/\1/p' $(filepath-constants)),$($(def-pref)$(sec-pref)$(1))))
endef

#######
###
#   Assign the (T,C,N) security parameters variables
###
#######

security-parameters := T N
$(sec-pref)T := $(call security_parameter,T)
$(sec-pref)N := $(call security_parameter,N)
$(sec-pref)C := $($(sec-pref)T)

#######
###
#   Standard targets
###
#######

.PHONY: all 

all::;

#######
###
#   Phony targets
###
#######

.PHONY: security-parameters

security-parameters:
	@printf "%s = %s\n" $(security-parameter-keys) $(security-parameter-vals)

security-parameter-keys:
	@printf "( %03s, %03s, %03s )\n" T C N

security-parameter-vals:
	@printf "( %03s, %03s, %03s )\n" "$($(sec-pref)T)" "$($(sec-pref)C)" "$($(sec-pref)N)"

endif # IMPORT_MAKE_PARAMETERS
