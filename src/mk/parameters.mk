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

ltl-property-labels := HLT FSU PCS

$(def-pref)ltl-property     := $(firstword $(ltl-property-labels))
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
#   Assign the LTL property
###
#######

ifdef LTL
ifneq (,$(findstring $(LTL),$(ltl-property-labels)))
ltl-property := $(LTL)
else
ltl-property := $($(def-pref)ltl-property)
endif
else
ltl-property := $($(def-pref)ltl-property)
endif

#######
###
#   Assign the protocol version
###
#######

protocol-name         := TreeKEM
protocol-version-pref := v

ifndef version
protocol-version := $(protocol-version-pref)$($(def-pref)protocol-version)
else
protocol-version := $(protocol-version-pref)$(version)
endif

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

.PHONY: show-ltl-property show-protocol-version show-security-parameters show-security-parameter-keys show-security-parameter-vals

show-ltl-property:
	@printf "LTL property = ( %s )" $(ltl-property)

show-protocol-version:
	@printf "$(protocol-version)"

show-security-parameters:
	@printf "%s = %s\n" $(security-parameter-keys) $(security-parameter-vals)

show-security-parameter-keys:
	@printf "( %03s, %03s, %03s )\n" T C N

show-security-parameter-vals:
	@printf "( %03s, %03s, %03s )\n" "$($(sec-pref)T)" "$($(sec-pref)C)" "$($(sec-pref)N)"

endif # IMPORT_MAKE_PARAMETERS
