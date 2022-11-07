ifndef IMPORT_MAKE_ENVIRONMENT
IMPORT_MAKE_ENVIRONMENT := 1

#######
###
#   Environmental Constants
###
#######


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

ifndef IMPORT_MAKE_COMPILATION
IMPORT_MAKE_COMPILATION := 1

#######
###
#   Conditionl Redefinitions
###
#######

basename-encoding    ?= pan
extension-makefile   ?= mk
extension-promela    ?= pml
dir-binaries         ?= ./
dir-make-definitions ?= ./
dir-output-encoding  ?= ./
dir-protocol-model   ?= ./
dir-backup-record    ?= ./records/
dir-backup-trail     ?= ./trails/

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := infostr sources
filename-dependancies := gmsl $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables for COMPILATION
###
#######

extension-verifier := model
basename-verifier  := $(info-string)
filename-verifier  := $(basename-verifier).$(extension-verifier)
filepath-verifier  := $(abspath $(addprefix $(dir-binaries),$(filename-verifier)))
pattern-verifier   := $(dir-binaries)$(info-string-pattern).$(extension-verifier)
sources-verifier   := $(filepath-modeling-code) $(filepath-encoding-code)

extension-trail  := trail
basename-trail   := $(info-symbol)
filename-trail   := $(basename-trail).$(extension-trail)
filepath-trail   := $(abspath $(filename-trail))

extension-record := log
basename-record  := $(info-symbol)
filename-record  := $(basename-record).$(extension-record)
filepath-record  := $(abspath $(filename-record))

#######
###
#   Multi-core computation parameter
###
#######

param-cores := 4
ifdef cores
param-cores := $(cores) 
endif

#######
###
#   Multi-core computation parameter
###
#######

param-vector := 768
ifdef vector
param-vector := $(vector) 
endif

param-min-dfa := No
ifdef DFA
param-min-dfa := $(DFA)
endif

#######
###
#   Memory allocation parameter(s)
###
#######

basis-memory-encoded := 1024 # Binary base
extra-memory-encoded := 2048 # Mebibyte(s)
param-memory-encoded := 20   # Gibibyte(s)
alloc-memory-encoded := $(call multiply,$(basis-memory-encoded),$(param-memory-encoded))
ifdef memory
# NOTE:
# Memory is specified by users in GiB, but accepted by SPIN in MiB.
ifneq (,$(findstring G,$(memory)))
#$(info Gibi branch $(memory))
param-memory-encoded := $(subst G,,$(memory))
alloc-memory-encoded := $(call multiply,$(basis-memory-encoded),$(param-memory-encoded))
# NOTE:
# Memory is specified by users in MiB
else
#$(info Mebi branch $(memory))
alloc-memory-encoded := $(memory)
param-memory-encoded := $(call divide,$(alloc-memory-encoded),$(basis-memory-encoded))
endif
endif
usage-memory-encoded := $(call plus,$(alloc-memory-encoded),$(extra-memory-encoded))


# Max RAM allocation of program in MiB
alloc-memory := $(alloc-memory-encoded)

# Max RAM Usage of PBS script in MiB
usage-memory := $(usage-memory-encoded)

# Max RAM allocation of program in GiB
param-memory := $(param-memory-encoded)

#$(info Alloc: $(alloc-memory) MiB)
#$(info Usage:    $(usage-memory) MiB)
#$(info Param:    $(param-memory) GiB)

#######
###
#   Compilation directives
###
#######

opt-properties := \
#    -DPRINTF \
#    -DREACH

ifeq ("$(param-min-dfa)","Yes")
opt-memory := \
    -DMA=$(param-vector) \
    -DSPACE
endif

opt-random := \
    -DP_RAND=1618033988 \
    -DT_RAND=1155727349

opt-thread := \
    -DMEMLIM=$(alloc-memory) \
    -DNCORE=$(param-cores) \
    -DPMAX=2 \
    -DQMAX=0

opt-timing := \
    -DNOBOUNDCHECK \
    -DNOFAIR \
    -DXUSAFE \
    -DSEP_STATE \
#    -DSAFETY

opt-vector := \
    -DCOLLAPSE \
    -DVECTORSZ=$(param-vector)

directives-glue := $(SPACE)\$(NEWLINE)$(SPACE)$(SPACE)

directives-list := $(strip $(opt-random) $(opt-timing) $(opt-thread) $(opt-vector) $(opt-memory) $(opt-properties))

directives-rows := $(subst $(SPACE),$(directives-glue),$(directives-list))

#######
###
#   Standard targets
###
#######

.PHONY: all check clean install installcheck installdirs

all:: $(filepath-verifier)

check:: verification

clean::
	@-rm -f $(pattern-verifier)

install:: $(filepath-verifier)

installcheck:: verification

installdirs:: $(dir-binaries) $(dir-backup-record) $(dir-backup-trail)

#######
###
#   Phony targets
###
#######

.PHONY: backup compile find-verifier show-directives verification

backup: $(dir-backup-record) $(dir-backup-trail)
	@mv  --backup=numbered \
	    --suffix='backup-' \
	    $(filepath-record) $(dir-backup-record) 2>/dev/null || true
	@mv  --backup=numbered \
	    --suffix='backup-' \
	    $(filepath-trail) $(dir-backup-trail) 2>/dev/null || true

compile: $(filepath-verifier)
	@printf "\nCompiled model analysis binary located at:\n\t%s\n" "$(filepath-verifier)"

find-verifier:
	@printf "%s\n" "$(filepath-verifier)"

show-directives:
	@printf "%s" "$(directives-list)"

verification: $(filepath-verifier) backup
	$(filepath-verifier) -a -v -x > $(filepath-record)

#######
###
#   Build target specifications
###
#######

$(dir-binaries):
	mkdir -p $@

$(dir-backup-record):
	mkdir -p $@

$(dir-backup-trail):
	mkdir -p $@

$(filepath-verifier): $(dir-binaries) $(sources-verifier)
	$(info $(sources-verifier))
	$(subst $(SPACE),$(directives-glue),gcc $(directives-list)) \
	-O3 \
	-o $@ \
	$(filepath-encoding-in-C)

endif # IMPORT_MAKE_COMPILATION
