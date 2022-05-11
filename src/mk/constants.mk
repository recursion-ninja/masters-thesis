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

ifndef IMPORT_MAKE_CONSTANTS
IMPORT_MAKE_CONSTANTS := 1

#######
###
#   Conditionl Redefinitions
###
#######

dir-protocol-model ?= ./
extension-makefile ?= mk
extension-promela  ?= pml

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
#   Variables for CONSTANTS
###
#######

con-pair := $(COMMA)
con-pref := const-
con-temp := breif-

#######
###
#   Custom function definitions for CONSTANTS
###
#######

define amend_definitions_within
	@if [ -n "$(amendment-mapping)" ]; then \
	printf "\nAmending constants within:\n\t%s\n\nAmendments:\n" "$(1)"; \
	fi
	@for kvp in $(amendment-mapping); do \
	    key=$${kvp%,*}; \
	    val=$${kvp#*,}; \
	    rep="/^#define/s/\\s+$${key}(\\s+)[[:digit:]]+\\s*$$/ $${key}\\1$${val}/"; \
	    printf "\t%-13s-->%4s\n" "$${key}" "$${val}"; \
	    sed -E -i "$${rep}" $(1); \
	done
	@if [ -n "$(amendment-mapping)" ]; then echo ""; fi
endef

define bits_required
$(shell echo "scale=3; l($(1))/l(2)" | bc -l | cut -f1 -d'.' | xargs -n 1 -I "%" echo "scale=0; " "%" " + 1" | bc)
endef

#######
###
#   Variables derived from the (T,C,N) security parameters
###
#######

# Conditionally assign security parameter values if they were passed from the command line.
# Compute the bit widths required for the supplied security parameter(s).
# Compute the constants values which are derivative of the supplied security parameter(s).

# Security parameter: (T)
$(con-pref)T            := $($(sec-pref)T)
$(con-pref)BITS_T       := $(call bits_required,$(shell expr $($(con-pref)T) - 1))
$(con-pref)BITS_EPOCH   := $(call bits_required,$($(con-pref)T))
$(con-pref)FIRST_EPOCH  := 0
$(con-pref)FINAL_EPOCH  := $(shell expr $($(con-pref)T) - 1)
$(con-pref)NEVER        := $(shell expr $$(( ( 1 << $($(con-pref)BITS_EPOCH) ) - 1 )) )

# Security parameter: (C)
$(con-pref)C            := $($(sec-pref)C)
$(con-pref)BITS_C       := $(call bits_required,$(shell expr $($(con-pref)C) - 1))
$(con-pref)MAX_REVEAL   := $(shell expr $($(con-pref)C) - 1)

# Security parameter: (N)
$(con-pref)N            := $($(sec-pref)N)
$(con-pref)BITS_N       := $(call bits_required,$(shell expr $($(con-pref)N) - 1))
$(con-pref)BITS_USERID  := $(call bits_required,$($(con-pref)N))
$(con-pref)BITS_VERTEX  := $(shell expr $($(con-pref)BITS_N) + 1)
$(con-pref)NONE         := $(shell echo $$(( (1 << $($(con-pref)BITS_USERID)) - 1 )) )
$(con-pref)TREE_ORDER   := $(shell echo $$(( (1 << $($(con-pref)BITS_VERTEX)) - 1 )) )
$(con-pref)ROOT         := 0
$(con-pref)LEAF         := $(shell expr $($(con-pref)TREE_ORDER) / 2)
$(con-pref)FIRST_USERID := 0
$(con-pref)FINAL_USERID := $(shell expr $($(con-pref)N) - 1)
$(con-pref)FIRST_VERTEX := 0
$(con-pref)FINAL_VERTEX := $(shell expr $($(con-pref)TREE_ORDER) - 1)

# Collect all defined constant variables and construct a key-value pair mapping
defined-constants := $(sort $(filter $(con-pref)%,$(.VARIABLES)))
amendment-mapping := $(subst $(con-pref),,$(foreach def-const,$(defined-constants),$(def-const)$(con-pair)$($(def-const))))

#######
###
#   Standard targets
###
#######

.PHONY: all amend-constants

all::;

#######
###
#   Phony targets
###
#######

amend-constants: $(filepath-constants)
	$(call amend_definitions_within,$<)

endif # IMPORT_MAKE_CONSTANTS
