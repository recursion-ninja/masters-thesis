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
dir-backup           ?= ./trails
dir-binaries         ?= ./
dir-make-definitions ?= ./
dir-output-encoding  ?= ./
dir-protocol-model   ?= ./

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

extension-verifier := analysis
basename-verifier  := $(infostr)
filename-verifier  := $(basename-verifier).$(extension-verifier)
filepath-verifier  := $(abspath $(addprefix $(dir-binaries),$(filename-verifier)))
pattern-verifier   := $(abspath $(addprefix $(dir-binaries),$(infostr-pattern).$(extension-verifier)))
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

#model-specification      := Model-Specification
#filename-modeling-spec   := $(model-specification).$(extension-promela)
#filename-modeling-code   := $(wildcard $(dir-protocol-model)*$(extension-promela))
#filepath-modeling-spec   := $(abspath $(addprefix $(dir-protocol-model),$(filename-modeling-spec)))
#filepath-modeling-code   := $(abspath $(filename-modeling-code))
#
#extensions-encoding-in-C := c h
#extensions-encoding-code := $(sort b m p t $(extensions-encoding-in-C))
#
#filename-encoding-in-C   := $(addprefix $(basename-encoding).,$(extensions-encoding-in-C))
#filename-encoding-code   := $(addprefix $(basename-encoding).,$(extensions-encoding-code))
#filepath-encoding-in-C   := $(sort $(abspath $(addprefix $(dir-output-encoding),$(filename-encoding-in-C))))
#filepath-encoding-code   := $(sort $(abspath $(addprefix $(dir-output-encoding),$(filename-encoding-code))))

#######
###
#   Standard targets
###
#######

.PHONY: all clean install installdirs

all:: $(filepath-verifier)

clean::
	rm -f  $(pattern-verifier) $(log-to-out) $(log-to-err)

install:: $(filepath-verifier)

installdirs:: $(dir-binaries) $(dir-trail-backup)

#######
###
#   Phony targets
###
#######

.PHONY: backup verification

backup: $(dir-trail-backup)
	mv  --backup=numbered \
	    --suffix='backup-' \
	    $(trail-file) $(backup-dir)/$(trail-file) 2>/dev/null || true

verification: $(filepath-verifier) backup
	$(filepath-verifier) -a -i
	@$(MAKE) --no-print-directory backup

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
	gcc -O3 $(directives) -o $@ $(filepath-encoding-in-C)

endif # IMPORT_MAKE_COMPILATION
