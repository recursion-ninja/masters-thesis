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
filename-makefile-parts  := gmsl $(addsuffix .$(extension-makefile),$(basename-makefile-parts))
filepath-makefile-parts  := $(abspath $(addprefix $(dir-make-definitions),$(filename-makefile-parts)))
filepath-makefile-gmsl   := $(abspath $(addprefix $(dir-make-definitions),__gmsl))


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

logging-output-pattern := $(info-symbol-pattern).*.log

cluster-output-pattern := $(info-string-pattern)/$(logging-output-pattern)
cluster-trails-pattern := *.$(info-symbol-pattern).trail
cluster-detail-pattern := $(subst $(SPACE),$(info-string-glue),$(info-string-prefix) $(protocol-name) *)
cluster-finish-pattern := $(info-string-pattern) runtime:


cluster-working-directory := '$${HOME}/$(filename-bundle)'
cluster-filepath-script   := '$${HOME}/$(filename-bundle)/$(filename-bundle-pbs)'
cluster-options :=\
    -j oe \
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
sshpass -p $(cluster-pass) scp -Cpr $(1) $(2) && echo "    FROM: $(1)\n    TO:   $(2)\n"
endef

define ssh-with
sshpass -p $(cluster-pass) ssh $(cluster-auth) '$(1)'
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

.PHONY: ask-password cluster-bundle cluster-connect cluster-pull cluster-pull-logs cluster-pull-trails cluster-push scp-with

ask-password:
ifeq ($(cluster-pass),)
	@$(eval cluster-pass=$(shell stty -echo; read -p "Password for $(cluster-auth): " secret; stty echo; echo $$secret))
	@echo ""
endif

cluster-bundle: $(filepath-bundle-complete)
	@echo "\nBundle created at:\n\t$(filepath-bundle)"

cluster-connect: ask-password
	@$(call ssh-with)


cluster-pull: ask-password cluster-pull-logs cluster-pull-trails

cluster-pull-logs:
	@$(eval final-logs=$(sort $(strip $(shell $(call ssh-with,find $(cluster-detail-pattern) -type f -name "$(logging-output-pattern)" -exec grep -l "$(cluster-finish-pattern)" {} +)))))
	@printf "  Complete verification logs: %3d found\n\n" "$(words $(final-logs))"
	@$(foreach log-file,$(final-logs),$(call scp-with,'$(cluster-auth):./$(log-file)',$(dir-logging));)

cluster-pull-trails:
	@$(eval found-trails=$(sort $(strip $(shell $(call ssh-with,find $(cluster-detail-pattern) -type f -name "$(cluster-trails-pattern)")))))
	@printf "  Counterexample trail files: %3d found\n\n" "$(words $(found-trails))"
	@$(foreach trail-file,$(found-trails),$(call scp-with,'$(cluster-auth):./$(trail-file)',$(dir-logged-trails));)

cluster-push: $(filepath-bundle-complete) ask-password
	@echo "Transferring:"
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

$(filepath-bundle-mkparts): $(filepath-makefile-parts) $(filepath-makefile-gmsl)
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
	  --variable=allocs:$(param-memory) \
	  --variable=cores:$(param-cores) \
	  --variable=memory:$(usage-memory) \
	  --variable=name:$(info-symbol) \
	  --variable=property:$(ltl-property) \
	  --write=plain

endif # IMPORT_MAKE_CLUSTER
