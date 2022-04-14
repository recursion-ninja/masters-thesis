ifndef IMPORT_MAKE_ENVIRONMENT
IMPORT_MAKE_ENVIRONMENT ::= 1

#######
###
#   Environmental Constants
###
#######

.ONESHELL:
.DEFAULT:;
SHELL ::= /bin/sh
COMMA ::= ,
EMPTY ::=
SPACE ::= $(EMPTY) $(EMPTY)

endif # IMPORT_MAKE_ENVIRONMENT

ifndef IMPORT_MAKE_CONSTANTS
IMPORT_MAKE_CONSTANTS ::= 1

#######
###
#   Conditionl Redefinitions
###
#######

dir-protocol-model ?= ./
extension-promela  ?= pml

#######
###
#   Variables for TRANSPILE
###
#######

basename-constants ::= Parameterized-Constants
filename-constants ::= $(addsuffix .$(extension-promela),$(basename-constants))
filepath-constants ::= $(abspath $(addprefix $(dir-protocol-model),$(filename-constants)))

def-pref ::= const-
def-pair ::= $(COMMA)

default-version ::= 1.0

infostr-glue             ::= _
infostr-model-name       ::= $(subst $(SPACE),$(infostr-glue),CGKA Model)
infostr-security-keys    ::= $(subst $(SPACE),$(infostr-glue),T C N)
infostr-protocol-name    ::= $(subst $(SPACE),$(infostr-glue),TreeKEM v)
ifndef version
infostr-protocol-version ::= $(default-version)
else
infostr-protocol-version ::= $(version)
endif

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
	$$(shell echo "scale=3; l($(1))/l(2)" | bc -l | cut -f1 -d'.' | xargs -n 1 -I "%" echo "scale=0; " "%" " + 1" | bc)
endef

#######
###
#   Phony targets
###
#######

.INTERMEDIATE: assign-constants
.PHONY: all amend-constants assign-infostr

all::;

amend-constants: $(filepath-constants) assign-constants
	$(call amend_definitions_within,$<)

assign-constants:
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
	@$(eval $(def-pref)BITS_N       ::= $(call bits_required,$(shell expr $($(def-pref)N) - 1)))
	@$(eval $(def-pref)BITS_USERID  ::= $(call bits_required,$($(def-pref)N)))
	@$(eval $(def-pref)BITS_VERTEX  ::= $(shell expr $($(def-pref)BITS_N) + 1))
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


assign-infostr: $(filepath-constants) amend-constants
	@$(eval security-vals ::= \
	$(foreach key,$(subst \
	    $(infostr-glue),$(SPACE),$(infostr-security-keys)),$(shell \
	        sed -n 's/^#define $(key) \(.*\) *$$/\1/p' $<)))
	@$(eval infostr-security-values  ::= $(subst $(SPACE),$(infostr-glue),$(security-vals)))
	@$(eval infostr-protocol-version ::= $(default-version))
	@$(eval infostr-all-components   ::= \
	    $(infostr-model-name) \
	    $(infostr-protocol-name)$(infostr-protocol-version) \
	    $(infostr-security-keys) \
	    $(infostr-security-values))
	@$(eval infostr ::= $(subst $(SPACE),-,$(infostr-all-components)))
	$(info $(infostr))

endif # IMPORT_MAKE_CONSTANTS
