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

ltl-property-labels := FSU PCS

$(def-pref)ltl-property     := $(firstword $(ltl-property-labels))
$(def-pref)protocol-version := 1
$(def-pref)$(sec-pref)N     := 8


basename-constants := Parameterized-Constants
filename-constants := $(addsuffix .$(extension-promela),$(basename-constants))
filepath-constants := $(abspath $(addprefix $(dir-protocol-model),$(filename-constants)))

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
protocol-version-num := $($(def-pref)protocol-version)
else
protocol-version-num := $(version)
endif

protocol-version := $(protocol-version-pref)$(protocol-version-num)

#######
###
#   Assign the (T,C,N) security parameters variables
###
#######

security-parameters := N

ifndef N
$(sec-pref)N := $($(def-pref)$(sec-pref)N)
else
$(sec-pref)N := $(N)
endif

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
