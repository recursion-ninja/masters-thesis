ifndef IMPORT_MAKE_TRANSPILE
IMPORT_MAKE_TRANSPILE ::= 1

.ONESHELL:
SHELL ?= /bin/bash

dependancies         := constants.mk
dir-make-definitions ?= .
extension-makefile   ?= mk

-include $(abspath $(addprefix $(dir-make-definitions)/,$(addsuffix .$(extension-makefile),$(dependancies))))


#######
###
#   Pre-defined values
###
#######

encoding-basename   ?= pan
extension-promela   ?= pml 
dir-protocol-model  ?= .
dir-output-encoding ?= .

filename-modeling-spec ::= model-specification.$(extension-promela)
filename-modeling-code ::= $(wildcard $(dir-protocol-model)/*$(extension-promela))
filepath-modeling-spec ::= $(abspath $(addprefix $(dir-protocol-model)/,$(filename-modeling-spec)))
filepath-modeling-code ::= $(abspath $(filename-modeling-code))

extensions-encoding-in-C ::= c h
extensions-encoding-code ::= $(sort b m p t $(extensions-encoding-in-C))

filename-encoding-in-C ::= $(addprefix $(encoding-basename).,$(extensions-encoding-in-C))
filename-encoding-code ::= $(addprefix $(encoding-basename).,$(extensions-encoding-code))
filepath-encoding-in-C ::= $(sort $(abspath $(addprefix $(dir-output-encoding)/,$(filename-encoding-in-C))))
filepath-encoding-code ::= $(sort $(abspath $(addprefix $(dir-output-encoding)/,$(filename-encoding-code))))

.INTERMEDIATE: token-encoding-code
.PHONY: all transpile


#######
###
#   Phony targets
###
#######

transpile: $(filepath-encoding-code)


#######
###
#   Build target specifications
###
#######

$(filepath-encoding-code): token-encoding-code

token-encoding-code: $(filepath-modeling-code)
	@$(MAKE) --no-print-directory amend-constants $(MAKEFLAGS)
#	Setup the temporary compilation environment
	@$(eval dir-transpile ::= $(shell mktemp -d -t transpile-XXXXXXXXXX))
	@$(eval dir-initial   ::= $(shell pwd))
#	Transfer requisite source files and working location
	@mkdir -p $(dir-output-encoding)
	@for file in $(filepath-modeling-code); do \
	    cp $$file $(dir-transpile); \
	done
	@cd $(dir-transpile)
#	Transpile specification to C code encoding
	spin -a $(filepath-modeling-spec)
	@cat <(echo "#include <stdio.h>") $(encoding-basename).h > $(encoding-basename).h.temp
	@mv $(encoding-basename).h.temp $(encoding-basename).h
#	Copy C code encoding files to 'encoding directory'
	@$(eval commalist-encoding-code ::= $(shell tr ' ' ',' <<<"./{$(filename-encoding-code)}"))
	@cp $(commalist-encoding-code) $(abspath $(dir-output-encoding))
	@cd $(dir-initial)


endif # IMPORT_MAKE_TRANSPILE
