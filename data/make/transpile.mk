ifndef IMPORT_MAKE_ENVIRONMAENT
IMPORT_MAKE_ENVIRONMENT := 1

#######
###
#   Environmental Constants
###
#######


#.DEFAULT:;
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
basename-benchmark   ?= benchmark-series
extension-makefile   ?= mk
extension-promela    ?= pml 
dir-make-definitions ?= ./
dir-output-encoding  ?= ./
dir-protocol-model   ?= ./
dir-benchmark-series ?= ./

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := constants properties sources
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)


transpile-bunch-filepath := $(abspath $(dir-distribution)$(info-string))/

transpile-model-filename := Model.$(extension-promela)
transpile-model-filepath := $(transpile-bunch-filepath)$(transpile-model-filename)

transpile-bench-job-filename := $(basename-benchmark).run
transpile-bench-job-filepath := $(transpile-bunch-filepath)$(transpile-bench-job-filename)

transpile-bench-ext-filename := sh script template
transpile-bench-src-filename := $(addprefix $(basename-benchmark).,$(transpile-bench-ext-filename))
transpile-bench-src-filepath := $(addprefix $(dir-benchmark-series),$(transpile-bench-src-filename))


#transpile-mainC-filename := $(basename-encoding).c
#transpile-mainC-filepath := $(transpile-bunch-filepath)$(transpile-mainC-filename)

transpile-extra-filename := $(addprefix $(basename-encoding).,$(extensions-encoding-code))
transpile-extra-filepath := $(addprefix $(transpile-bunch-filepath),$(transpile-extra-filename))




#######
###
#   Standard targets
###
#######

.PHONY: all benchmark-series clean install installdirs transpile

all:: benchmark-series

clean::
	@-rm -f \
	  $(wildcard $(abspath $(dir-distribution))/*) \
	  $(filepath-encoding-pattern)

install:: benchmark-series

installdirs:: $(transpile-bunch-filepath)

#######
###
#   Phony targets
###
#######

benchmark-series: token-encoding-code $(transpile-bench-job-filepath)

.INTERMEDIATE: token-encoding-code
token-encoding-code: amend-constants $(transpile-bunch-filepath) $(filepath-modeling-code)
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
	    spin -a $(filename-modeling-spec); \
	    echo "#include <stdio.h>" > $(tmp-transpile); \
	    cat $(mod-transpile)     >> $(tmp-transpile); \
	    mv  $(tmp-transpile) $(mod-transpile); \
	    cp $(filename-encoding-code) $(transpile-bunch-filepath); \
	    cp $(filename-encoding-code) $(abspath $(dir-output-encoding)); \
	)
	@rm -fr $(dir-transpile)


#######
###
#   Build target specifications
###
#######

$(filepath-modeling-spec):;

$(filepath-encoding-code):   token-encoding-code

$(transpile-extra-filepath): token-encoding-code

$(dir $(transpile-model-filepath)):
	mkdir -p $@

$(transpile-bench-job-filepath): $(transpile-bench-src-filepath) $(dir $(transpile-bench-job-filepath))
	$< -n $($(sec-pref)N) -p $(ltl-property) -v $(protocol-version-num) 
	cp $(patsubst %.sh,%.run,$<) $@

#$(transpile-model-filepath): $(filepath-modeling-spec) $(dir $(transpile-model-filepath))
#	( \
#	    cd $(dir $<); \
#	    cpp $< > $@; \
#	    sed -i'.bak' 's/^#\s[^\n]\+$//g' "${FILEPATH_MODEL}";
#	    sed -i'.bak' 'N;/^\n$/d;P;D' "${FILEPATH_MODEL}";
#	)

endif # IMPORT_MAKE_TRANSPILE
