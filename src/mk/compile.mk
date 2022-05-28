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

#######
###
#   Memory allocation parameter(s)
###
#######

# NOTE:
# Memory is specified by users in GiB, but accepted by SPIN in MiB.
basis-memory-encoded := $(call int_encode,1024) # Binary base
extra-memory-encoded := $(call int_encode,1)    # Gibibyte(s)
param-memory-encoded := $(call int_encode,20)   # Gibibyte(s)
ifdef memory
param-memory-encoded := $(call int_encode,$(memory))
endif
alloc-memory-encoded := $(call int_multiply,$(basis-memory-encoded),$(param-memory-encoded))
usage-memory-encoded := $(call     int_plus,$(param-memory-encoded),$(extra-memory-encoded))


# Max RAM allocation of program in MiB
alloc-memory := $(call int_decode,$(alloc-memory-encoded))

# Max RAM allocation of program in GiB
param-memory := $(call int_decode,$(param-memory-encoded))

# Max RAM Usage of PBS script in MiB
usage-memory := $(call int_decode,$(usage-memory-encoded))

#######
###
#   Compilation directives
###
#######

opt-memory := \
    -DSPACE

opt-properties := #\
    -DREACH

opt-thread := \
    -DMEMLIM=$(alloc-memory) \
    -DNCORE=$(param-cores)

opt-timing := \
    -DNOBOUNDCHECK \
    -DNOFAIR \
    -DSEP_STATE \
    -DXUSAFE

opt-vector := \
    -DCOLLAPSE \
    -DMA=$(param-vector) \
    -DVECTORSZ=$(param-vector)


directives-glue := $(SPACE)\$(NEWLINE)$(SPACE)$(SPACE)

directives-list := $(strip $(opt-properties) $(opt-memory) $(opt-timing) $(opt-thread) $(opt-vector))

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
	$(filepath-verifier) -a -i -v -x > $(filepath-record)

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
	gcc $(directives-glue) $(directives-rows) \
	-O3 \
	-o $@ \
	$(filepath-encoding-in-C)

endif # IMPORT_MAKE_COMPILATION
