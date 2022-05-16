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

ifndef IMPORT_MAKE_CLUSTER
IMPORT_MAKE_CLUSTER := 1

#######
###
#   Conditionl Redefinitions
###
#######

basename-encoding    ?= pan
basename-encoding    ?= pbs
extension-makefile   ?= mk
extension-promela    ?= pml
dir-backup           ?= ./trails
dir-binaries         ?= ./
dir-distribution     ?= ./
dir-make-definitions ?= ./
dir-output-encoding  ?= ./
dir-pbs-script-parts ?= ./
dir-protocol-model   ?= ./
dir-source-code      ?= ./

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := compile transpile
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables for CLUSTER
###
#######

dir-logged-trails := $(abspath $(dir-logging)$(dir-backup))/


# Distribution to be moved to cluster
filename-bundle := $(info-string)
filepath-bundle := $(abspath $(addprefix $(dir-distribution),$(filename-bundle)))

# Pattern for matching any distribution
filename-bundle-pattern  := $(info-string-pattern)
filepath-bundle-pattern  := $(abspath $(addprefix $(dir-source-code),$(filename-bundle-pattern)))

# Distribution's PBS script file
prefname-pbs             := pbs.
prefpath-pbs             := $(abspath $(dir-pbs-script-parts)/$(prefname-pbs))
filepath-pbs-body        := $(prefpath-pbs)script
filepath-pbs-config      := $(abspath $(shell mktemp -d -t $(prefname-pbs)-XXXXXXXXXX)/config)
filepath-pbs-defaults    := $(prefpath-pbs)defaults
filepath-pbs-template    := $(prefpath-pbs)template

basename-makefile-parts  := compile infostr parameters sources
filename-makefile-parts  := $(addsuffix .$(extension-makefile),$(basename-makefile-parts))
filepath-makefile-parts  := $(abspath $(addprefix $(dir-make-definitions),$(filename-makefile-parts)))

filename-bundle-code     := $(notdir $(sources-verifier))
filepath-bundle-code     := $(abspath $(addprefix $(filepath-bundle)/,$(filename-bundle-code)))
filename-bundle-pbs      := pbs.sh
filepath-bundle-pbs      := $(abspath $(filepath-bundle)/$(filename-bundle-pbs))
filepath-bundle-makefile := $(abspath $(filepath-bundle)/makefile)
filepath-bundle-mkparts  := $(abspath $(addprefix $(filepath-bundle)/,$(filename-makefile-parts)))

filepath-bundle-complete := \
    $(filepath-bundle-code) \
    $(filepath-bundle-makefile) \
    $(filepath-bundle-mkparts) \
    $(filepath-bundle-pbs)

cluster-host := ${CLUSTER_HOST}
cluster-user := ${CLUSTER_USER}
cluster-pass := ${CLUSTER_PASS}
cluster-auth := $(cluster-user)@$(cluster-host)
cluster-pbs  := $(process)$(cluster-pbs-suffix)

cluster-output-pattern := $(info-string-pattern)/$(info-symbol-pattern).*.log
cluster-trails-pattern := $(info-string-pattern)/*.$(info-symbol-pattern).trail


cluster-working-directory := '$${HOME}/$(filename-bundle)'
cluster-filepath-script   := '$${HOME}/$(filename-bundle)/$(filename-bundle-pbs)'
cluster-options :=\
    -o $(info-symbol).out.log \
    -wd $(cluster-working-directory)


ifndef LTL
ltl-property := Totality
else
ltl-property := $(LTL)
endif


#######
###
#   Custom function definitions for CLUSTER
###
#######

define scp-with
@sshpass -p $(cluster-pass) scp -pr $(1) $(2) && echo "\tFROM: $(1)\n\tTO:   $(2)\n"
endef

define ssh-with
@sshpass -p $(cluster-pass) ssh $(cluster-auth) '$(1)'
endef

#######
###
#   Standard targets
###
#######

.PHONY: all clean installdirs

all::;

clean::
	@-rm -fr $(dir-distribution)*

installdirs:: $(dir-distribution)

#######
###
#   Phony targets
###
#######

.PHONY: ask-password cluster-bundle cluster-connect cluster-pull cluster-push scp-with

ask-password:
ifeq ($(cluster-pass),)
	@$(eval cluster-pass=$(shell stty -echo; read -p "Password for $(cluster-auth): " secret; stty echo; echo $$secret))
	@echo ""
endif

cluster-bundle: $(filepath-bundle-complete)
	@echo "\nBundle created at:\n\t$(filepath-bundle)"

cluster-connect: ask-password
	@$(call ssh-with)


cluster-pull: ask-password
	@$(call scp-with,'$(cluster-auth):./$(cluster-output-pattern)',$(dir-logging))
	@$(call scp-with,'$(cluster-auth):./$(cluster-trails-pattern)',$(dir-logged-trails))

cluster-push: $(filepath-bundle-complete) ask-password
	@echo "Transfering:"
	@$(call scp-with,"$(filepath-bundle)","$(cluster-auth):./")

cluster-verify: cluster-push
	@$(call ssh-with,'qsub $(cluster-options) $(cluster-filepath-script)')


#######
###
#   Build target specifications
###
#######

$(filepath-bundle):
	@mkdir -p $@

$(filepath-bundle-code): $(sources-verifier)
	@mkdir -p $(dir $@)
	@cp    $^ $(dir $@)

$(filepath-bundle-makefile): $(filepath-bundle-mkparts)
	@echo '-include $(notdir $^)\n\nall:: verification' > $@

$(filepath-bundle-mkparts): $(filepath-makefile-parts)
	@mkdir -p $(dir $@)
	@cp    $^ $(dir $@)

$(filepath-bundle-pbs): $(filepath-pbs-config) $(filepath-pbs-body)
	@mkdir -p $(dir $@)
	@cat $^ > $@
	@chmod +x $@

$(filepath-pbs-config): $(filepath-pbs-defaults) $(filepath-pbs-template)
	@echo "" | pandoc \
	  --metadata-file=$(filepath-pbs-defaults) \
	  --output=$@ \
	  --read=markdown \
	  --template=$(filepath-pbs-template) \
	  --variable=cores:$(param-cores) \
	  --variable=memory:$(param-memory) \
	  --variable=name:$(info-symbol) \
	  --variable=property:$(ltl-property) \
	  --write=plain

endif # IMPORT_MAKE_CLUSTER
