ifndef IMPORT_MAKE_ENVIRONMENT
IMPORT_MAKE_ENVIRONMENT := 1

#######
###
#   Environmental Constants
###
#######


.DEFAULT:;
SHELL := /bin/bash
COMMA := ,
EMPTY :=
SPACE := $(EMPTY) $(EMPTY)

endif # IMPORT_MAKE_ENVIRONMENT

ifndef IMPORT_MAKE_TRANSPILE
IMPORT_MAKE_TRANSPILE := 1

#######
###
#   Conditionl Redefinitions
###
#######

basename-encoding    ?= pan
extension-makefile   ?= mk
extension-promela    ?= pml 
dir-make-definitions ?= ./
dir-output-encoding  ?= ./
dir-protocol-model   ?= ./

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := constants properties sources
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Standard targets
###
#######

.PHONY: all clean install installdirs transpile

all:: $(filepath-encoding-code)

clean::
	@-rm -f  $(filepath-encoding-pattern)

install:: $(filepath-encoding-code)

installdirs:: $(dir-output-encoding)

#######
###
#   Phony targets
###
#######

.INTERMEDIATE: token-encoding-code
token-encoding-code: amend-constants $(dir-output-encoding) $(filepath-modeling-code) $(filepath-property)
#	Setup the temporary compilation environment
	@$(eval dir-transpile := $(shell mktemp -d -t transpile-XXXXXXXXXX))
	@$(eval tmp-transpile := $(shell mktemp -t transpile-HEADER-XXX))
	@$(eval mod-transpile := $(filter %.h,$(filename-encoding-code)))
#	Transfer requisite source files and working location
	@cp -R $(filepath-modeling-code) $(dir-transpile)
#	1. Transpile specification to C code encoding
#	2. Add requisite yet missing include to C header file
#	3. Copy C code encoding files to 'encoding directory'
	@( \
	    cd $(dir-transpile); \
	    spin -a $(filename-modeling-spec) -F $(filepath-property); \
	    echo "#include <stdio.h>" > $(tmp-transpile); \
	    cat $(mod-transpile)     >> $(tmp-transpile); \
	    mv  $(tmp-transpile) $(mod-transpile); \
	    cp $(filename-encoding-code) $(abspath $(dir-output-encoding)); \
	)
	@rm -fr $(dir-transpile)

#######
###
#   Build target specifications
###
#######

$(dir-output-encoding):
	@-mkdir -p $@

$(filepath-encoding-code): token-encoding-code

endif # IMPORT_MAKE_TRANSPILE
