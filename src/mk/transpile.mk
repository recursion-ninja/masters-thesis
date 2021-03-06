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
token-encoding-code: amend-constants amend-properties $(dir-output-encoding) $(filepath-modeling-code)
#	Setup the temporary compilation environment
	@$(eval dir-transpile := $(shell mktemp -d -t transpile-XXXXXXXXXX))
	@$(eval dir-beginning := $(shell pwd))
#	Transfer requisite source files and working location
	@cp $(filter %.$(extension-promela),$^) $(dir-transpile)
	@cd $(dir-transpile)
#	Transpile specification to C code encoding
	spin -a $(filename-modeling-spec)
#	Add requisite yet missing include to C header file
	@$(eval tmp-transpile := $(shell mktemp -t transpile-HEADER-XXX))
	@$(eval mod-transpile := $(filter %.h,$(filename-encoding-code)))
	@echo "#include <stdio.h>" > $(tmp-transpile)
	@cat $(mod-transpile)     >> $(tmp-transpile)
	@mv  $(tmp-transpile) $(mod-transpile)
#	Copy C code encoding files to 'encoding directory'
	@cp $(filename-encoding-code) $(abspath $(dir-output-encoding))
	@cd $(dir-beginning)
	@-rm -fr $(dir-transpile)

#######
###
#   Build target specifications
###
#######

$(dir-output-encoding):
	@-mkdir -p $@

$(filepath-encoding-code): token-encoding-code

endif # IMPORT_MAKE_TRANSPILE
