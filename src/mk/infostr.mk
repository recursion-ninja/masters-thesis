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

ifndef IMPORT_MAKE_INFOSTR
IMPORT_MAKE_INFOSTR := 1

#######
###
#   Conditionl Redefinitions
###
#######

dir-protocol-model ?= ./
extension-makefile ?= mk

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := parameters
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables defining the "Information String"
###
#######

info-string-glue   := -
info-string-prefix := CGKA

info-string-substrings := \
$(info-string-prefix)\
$(protocol-name)\
$(protocol-version)\
$(ltl-property)\
$(foreach param,$(security-parameters),$(shell printf "$(param)%03d" $($(sec-pref)$(param))))

info-string-subpatterns := \
$(info-string-prefix)\
$(protocol-name)\
$(protocol-version-pref)[0-9]\
[A-Z][A-Z][A-Z]\
$(foreach param,$(security-parameters),$(param)[0-9][0-9][0-9])

info-string         := $(subst $(SPACE),$(info-string-glue),$(info-string-substrings))
info-string-pattern := $(subst $(SPACE),$(info-string-glue),$(info-string-subpatterns))
info-symbol         := $(subst $(SPACE),$(info-string-glue),$(wordlist 3,64,$(info-string-substrings)))
info-symbol-pattern := $(subst $(SPACE),$(info-string-glue),$(wordlist 3,64,$(info-string-subpatterns)))

#$(info $(NEWLINE)Unique Model Name:$(NEWLINE)$(TAB)$(info-string)$(NEWLINE)Unique Model Name:$(NEWLINE)$(TAB)$(info-symbol))

#######
###
#   Standard targets
###
#######

.PHONY: all

all::;

endif # IMPORT_MAKE_INFOSTR
