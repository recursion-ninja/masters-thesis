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

ifndef IMPORT_MAKE_PARSER
IMPORT_MAKE_PARSER := 1

#######
###
#   Conditionl Redefinitions
###
#######

extension-haskell     ?= hs
dir-binaries          ?= .
dir-parser-for-logs   ?= .

#######
###
#   Constants for PARSER
###
#######

filename-parser  := parse-table-row
filepath-parser  := $(abspath $(addprefix $(dir-binaries),$(filename-parser))) 

#######
###
#   Standard Targets
###
#######

.PHONY: all clean install installdirs

all:: $(filepath-parser)

clean::
	@-rm -f $(filepath-parser)
	@( cd $(dir-parser-for-logs) ; cabal clean )

install:: $(filepath-parser)

installdirs:: $(dir $(filepath-parser))

#######
###
#   Phony targets
###
#######

.PHONY: log-parser

log-parser: $(filepath-parser)

#######
###
#   Build Targets
###
#######

$(dir $(filepath-parser)):
	@mkdir -p $@

## Build thesis
$(filepath-parser): $(dir-parser-for-logs)
	( cd $(dir-parser-for-logs); cabal install --installdir=$(dir $@) --install-method=copy; )

endif # IMPORT_MAKE_PARSER
