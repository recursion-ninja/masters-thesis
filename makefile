ifndef IMPORT_MAKE_ENVIRONMENT
IMPORT_MAKE_ENVIRONMENT ::= 1

#######
###
#   Environmental Constants
###
#######

.ONESHELL:
.DEFAULT:;
SHELL ::= /bin/sh
COMMA ::= ,
EMPTY ::=
define NEWLINE

$(EMPTY)
endef
SPACE ::= $(EMPTY) $(EMPTY)
TAB   ::= $(shell printf '\011')

endif # IMPORT_MAKE_ENVIRONMENT

basename-encoding     ::= pan
basename-pbs-script   ::= pbs
extension-makefile    ::= mk
extension-markdown    ::= md
extension-promela     ::= pml
extension-portabledoc ::= pdf

dir-binaries          ::= ./bin/
dir-documents         ::= ./doc/
dir-logging           ::= ./log/
dir-source-code       ::= ./src/
dir-make-definitions  ::= $(abspath $(addprefix $(dir-source-code),$(extension-makefile)))/
dir-output-encoding   ::= $(abspath $(addprefix $(dir-source-code),$(basename-encoding)))/
dir-pbs-script-parts  ::= $(abspath $(addprefix $(dir-source-code),$(basename-pbs-script)))/
dir-protocol-model    ::= $(abspath $(addprefix $(dir-source-code),$(extension-promela)))/
dir-thesis-relative   ::= ./thesis/
dir-thesis-chapters   ::= $(abspath $(addprefix $(dir-source-code),$(addsuffix /$(dir-thesis-relative),$(extension-markdown))))/
dir-thesis-manuscript ::= $(abspath $(addprefix $(dir-documents),$(dir-thesis-relative)))/
dir-trail-backup      ::= $(abspath $(addprefix $(dir-logging),trails))

filepath-make-definitions ::= $(wildcard $(dir-make-definitions)*.$(extension-makefile))

$(info Including the following:\
  $(NEWLINE)$(TAB)$(subst $(SPACE),$(NEWLINE)$(TAB),$(notdir $(filepath-make-definitions))))

-include $(filepath-make-definitions)

all:: all-transpile
	@echo "Finished at top"
