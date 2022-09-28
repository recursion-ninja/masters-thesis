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

#######
###
#   Variables for PROPERTIES
###
#######
prop-prefix := LTL-

filename-property   := $(addprefix $(prop-prefix),$(addsuffix .$(extension-promela),$(ltl-property)))
filepath-property   := $(abspath $(addprefix $(dir-protocol-model),$(filename-property)))

basename-model-spec := Model-Specification
filename-model-spec := $(addsuffix .$(extension-promela),$(basename-model-spec))
filepath-model-spec := $(abspath $(addprefix $(dir-protocol-model),$(filename-model-spec)))

#######
###
#   Custom function definitions for PROPERTIES
###
#######

define alter_property_FSU
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

define amend_property_within
	@pattern="/^\\s*#include\\s\\+\"$(prop-prefix)\\(.*\\)\"/d"
	sed -i -e "$${pattern}" $(1)
	@echo '#include "$(filename-property)"' >> $(filepath-model-spec)
endef

#######
###
#   Standard targets
###
#######

.PHONY: all alter-properties amend-properties

all::;

#######
###
#   Phony targets
###
#######

alter-properties: $(filepath-property)
ifeq ($(ltl-property),$(word 2,$(ltl-property-labels)))
	$(call alter_property_FSU,$<)
endif

amend-properties: $(filepath-model-spec) $(filepath-property) alter-properties
	$(call amend_property_within,$<)

endif # IMPORT_MAKE_PROPERTIES
