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

ifndef IMPORT_MAKE_PROPERTIES
IMPORT_MAKE_PROPERTIES := 1

#######
###
#   Conditionl Redefinitions
###
#######

dir-make-definitions ?= ./
dir-protocol-model   ?= ./
extension-makefile   ?= mk
extension-promela    ?= pml

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := parameters
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

basename-properties := Parameterized-Properties
filename-properties := $(basename-properties).$(extension-promela)
filepath-properties := $(abspath $(addprefix $(dir-protocol-model),$(filename-properties)))

#######
###
#   Custom function definitions for CONSTANTS
###
#######

define amend_property_within
	@END_NUM=$(shell expr $($(sec-pref)T) - 2)
	@LTL_FSU=$$(mktemp -t LTL_FSU-XXXXXXXX)
	@echo "{" >> "$$LTL_FSU"
	@echo "    never_trivially_hoard_then_corrupt ->" >> "$$LTL_FSU"
	@for i in $$(seq 0 $$END_NUM); do
	    if [ "$$i" -eq "0" ]; then \
                printf "    (   future_secrecy_of_epoch( %2d )\\n" "$$i" >> "$$LTL_FSU"; \
	    else \
	        printf "    &&  future_secrecy_of_epoch( %2d )\\n" "$$i" >> "$$LTL_FSU"; \
	    fi \
	done
	@echo "    )" >> "$$LTL_FSU"
	@echo "}"     >> "$$LTL_FSU"
	@pattern="/^ltl\\s\\+FSU\\s*$$/,/[}]/ { /{/,/}/d }; /^ltl\\s\\+FSU\\s*$$/r $${LTL_FSU}"

	sed -i -e "$${pattern}" $(1)
	rm "$$LTL_FSU"
endef

#######
###
#   Standard targets
###
#######

.PHONY: all amend-properties

all::;

#######
###
#   Phony targets
###
#######

amend-properties: $(filepath-properties)
	$(call amend_property_within,$<)

endif # IMPORT_MAKE_PROPERTIES
