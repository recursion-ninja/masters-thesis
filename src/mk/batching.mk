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

ifndef IMPORT_MAKE_BATCH
IMPORT_MAKE_BATCH := 1

#######
###
#   Conditionl Redefinitions
###
#######

extension-haskell    ?= hs
extension-makefile   ?= mk
dir-binaries         ?= ./
dir-documents        ?= ./
dir-thesis-utilities ?= ./
dir-make-definitions ?= ./

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := cluster
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables for BATCH
###
#######

filename-batcher := cluster-send-batch
filepath-batcher := $(abspath $(dir-binaries)$(filename-batcher))

filename-mandate := mandate.config
filepath-mandate := $(abspath $(dir-documents)$(filename-mandate))

#######
###
#   Standard targets
###
#######

all:: $(filepath-batcher)

clean::
	@-rm -f $(filepath-batcher)
	@( cd $(dir-thesis-utilities) ; cabal clean )

install:: $(filepath-batcher)

#######
###
#   Phony targets
###
#######

.PHONY: cluster-batch-jobs cluster-batcher

cluster-batch-jobs: $(filepath-batcher) $(filepath-mandate)
	$< $(lastword $^)

cluster-batcher: $(filepath-batcher)

#######
###
#   Build Targets
###
#######

$(filepath-batcher): $(dir-thesis-utilities)
	( cd $(dir-thesis-utilities); cabal install $(notdir $@) --installdir=$(dir $@) --install-method=copy; )


endif # IMPORT_MAKE_BATCH
