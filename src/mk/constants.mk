ifndef IMPORT_MAKE_CONSTANTS
IMPORT_MAKE_CONSTANTS ::= 1
.ONESHELL:

#######
###
#   Constants
###
#######

dir-protocol-model ?= .

filename-constants ::= Parameterized-Constants
filepath-constants ::= $(abspath $(addprefix $(dir-protocol-model)/,$(addsuffix .$(extension-promela),$(filename-constants))))

def-pref ::= const-
def-pair ::= ,

infostr-security ::= $(EMPTY)

default-process ::= CGKA-TreeKEM
default-version ::= 1.0

ifndef process
process ::= $(default-process)
endif

ifndef version
version ::= $(default-version)
endif

define amend_definitions_within
	@printf "\nAmending constants within:\n\t%s\n\nAmendments:\n" "$(1)"
	@for kvp in $(amendment-mapping); do \
	    key=$${kvp%,*}; \
	    val=$${kvp#*,}; \
	    rep="/^#define/s/\\s+$${key}(\\s+)[[:digit:]]+\\s*$$/ $${key}\\1$${val}/"; \
	    printf "\t%-13s-->%4s\n" "$${key}" "$${val}"; \
	    sed -E -i "$${rep}" $(1); \
	done
	@echo ""
endef

define bits_required
	$$(shell echo "scale=3; l($(1))/l(2)" | bc -l | cut -f1 -d'.' | xargs -n 1 -I "%" echo "scale=0; " "%" " + 1" | bc)
endef

# Reset the default goal.
.DEFAULT_GOAL :=

.PHONY: all amend-constants assign-constants

all:;

amend-constants: assign-constants
ifndef AMENDED_CONSTANTS
	$(call amend_definitions_within,$(filepath-constants))
	@$(eval AMENDED_CONSTANTS ::= 1)
endif

assign-constants:
ifndef ASSIGNED_CONSTANTS
	@$(eval ASSIGNED_CONSTANTS ::= 1)
#	Conditionally assign security parameter values if they were passed from the command line.
#	Compute the bit widths required for the supplied security parameter(s).
#	Compute the constants values which are derivative of the supplied security parameter(s).
#
#	Security parameter: (T)
ifdef T
#	Process T parameter
	@$(eval $(def-pref)T     ::= $(T))
	@$(eval infostr-security ::= "$(infostr-security)T:$(T)")
#	Compute derivative constants of T
	@$(eval $(def-pref)BITS_T      ::= $(call bits_required,$(shell expr $($(def-pref)T) - 1)))
	@$(eval $(def-pref)BITS_EPOCH  ::= $(call bits_required,$($(def-pref)T)))
	@$(eval $(def-pref)FIRST_EPOCH ::= 0)
	@$(eval $(def-pref)FINAL_EPOCH ::= $(shell expr $($(def-pref)T) - 1))
	@$(eval $(def-pref)NEVER       ::= $(shell echo $$(( (1 << $($(def-pref)BITS_EPOCH) ) - 1))))
endif
#	Security parameter: (C)
ifdef C
#	Process C parameter
	@$(eval $(def-pref)C     ::= $(C))
	@$(eval infostr-security ::= "$(infostr-security)C:$(C)")
#	Compute derivative constants of C
	@$(eval $(def-pref)BITS_C ::= $(call bits_required,$(shell expr $($(def-pref)C) - 1)))
	@$(eval $(def-pref)MAX_REVEAL   ::= $(shell expr $($(def-pref)C) - 1))
endif
#	Security parameter: (N)
ifdef N
#	Process N parameter
	@$(eval $(def-pref)N     ::= $(N))
	@$(eval infostr-security ::= "$(infostr-security)N:$(N)")
#	Compute derivative constants of N
	@$(eval $(def-pref)BITS_N ::= $(call bits_required,$(shell expr $($(def-pref)N) - 1)))
	@$(eval $(def-pref)BITS_USERID ::= $(call bits_required,$($(def-pref)N)))
	@$(eval $(def-pref)BITS_VERTEX ::= $(shell expr $($(def-pref)BITS_N) + 1))
	@$(eval $(def-pref)NONE         ::= $(shell echo $$(( (1 << $($(def-pref)BITS_USERID)) - 1))))
	@$(eval $(def-pref)TREE_ORDER   ::= $(shell echo $$(( (1 << $($(def-pref)BITS_VERTEX)) - 1))))
	@$(eval $(def-pref)ROOT         ::= 0)
	@$(eval $(def-pref)LEAF         ::= $(shell expr $($(def-pref)TREE_ORDER) / 2))
	@$(eval $(def-pref)FIRST_USERID ::= 0)
	@$(eval $(def-pref)FINAL_USERID ::= $(shell expr $($(def-pref)N) - 1))
	@$(eval $(def-pref)FIRST_VERTEX ::= 0)
	@$(eval $(def-pref)FINAL_VERTEX ::= $(shell expr $($(def-pref)TREE_ORDER) - 1))
endif
#	Collect all defined constant variables and construct a key-value pair mapping
	@$(eval defined-constants ::= $(sort $(filter $(def-pref)%,$(.VARIABLES))))
	@$(eval amendment-mapping ::= $(subst $(def-pref),,$(foreach def-const,$(defined-constants),$(def-const)$(def-pair)$($(def-const)))))
endif


endif # IMPORT_MAKE_CONSTANTS
