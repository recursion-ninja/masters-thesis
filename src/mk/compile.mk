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
dir-trail-backup     ?= ./trails/

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := infostr sources
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables for COMPILATION
###
#######

extension-verifier := model
basename-verifier  := $(infostr-suffix)
filename-verifier  := $(basename-verifier).$(extension-verifier)
filepath-verifier  := $(abspath $(addprefix $(dir-binaries),$(filename-verifier)))
pattern-verifier   := $(dir-binaries)$(infostr-suffix-pattern).$(extension-verifier)
sources-verifier   := $(filepath-modeling-code) $(filepath-encoding-code)

extension-trail := trail
basename-trail  := $(infostr)
filename-trail  := $(basename-trail).$(extension-trail)
filepath-trail  := $(abspath $(filename-trail))

opt-memory := \
    -DCOLLAPSE \
    -DVECTORSZ=65536 #\
    -DMA=256

# 256 GB RAM
# 32 Cores
opt-thread := #\
    -DMEMLIM=262144 \
    -DNCORE=16

opt-timing := #\
    -DNOBOUNDCHECK \
    -DSAFETY

directives := \
    $(opt-memory) \
    $(opt-thread) \
    $(opt-timing) \

#######
###
#   Standard targets
###
#######

.PHONY: all clean install installdirs

all:: $(filepath-verifier)

clean::
	-rm -f  $(pattern-verifier)

install:: $(filepath-verifier)

installdirs:: $(dir-binaries) $(dir-trail-backup)

#######
###
#   Phony targets
###
#######

.PHONY: backup compile verification

backup: $(dir-trail-backup)
	mv  --backup=numbered \
	    --suffix='backup-' \
	    $(filepath-trail) $(dir-trail-backup) 2>/dev/null || true

compile: $(filepath-verifier)
	@printf "\nCompiled model analysis binary located at:\n\t%s\n" "$(filepath-verifier)"

verifier: $(filepath-verifier)
	@printf "%s\n" "$(filepath-verifier)"

verification: $(filepath-verifier) backup
	$(filepath-verifier) -a

#######
###
#   Build target specifications
###
#######

$(dir-binaries):
	mkdir -p $@

$(dir-trail-backup):
	mkdir -p $@

$(filepath-verifier): $(dir-binaries) $(sources-verifier)
	gcc -O3 \
	$(directives) \
	-o $@ \
	$(filepath-encoding-in-C)

endif # IMPORT_MAKE_COMPILATION
