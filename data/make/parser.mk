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
dir-thesis-utilities   ?= .

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
	@( cd $(dir-thesis-utilities) ; cabal clean )

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
$(filepath-parser): $(dir-thesis-utilities)
	( cd $(dir-thesis-utilities); cabal install $(notdir $@) --installdir=$(dir $@) --install-method=copy; )

endif # IMPORT_MAKE_PARSER
