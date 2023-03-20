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

ifndef IMPORT_MAKE_RESULTS
IMPORT_MAKE_RESULTS := 1

#######
###
#   Conditionl Redefinitions
###
#######

extension-makefile   ?= mk
dir-documents        ?= ./
dir-logging          ?= ./
dir-make-definitions ?= ./

#######
###
#   Dependent Make Definition(s)
###
#######

basename-dependancies := cluster parser
filename-dependancies := $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies := $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables for RESULTS
###
#######

logging-output-pattern := $(info-symbol-pattern).*.log

filename-results := results.csv
filepath-results := $(abspath $(addprefix $(dir-documents),$(filename-results)))

filename-outputs := $(wildcard $(dir-logging)$(logging-output-pattern))
filepath-outputs := $(abspath $(filename-outputs))

argument-demark  := $(SPACE)\$(NEWLINE)$(SPACE)$(SPACE)
argument-outputs := $(subst $(SPACE),$(argument-demark),$(sort $(strip $(filepath-outputs))))


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

all::

clean::
	@-rm -f $(filepath-results)

installdirs:: $(dir $(filepath-results))

#######
###
#   Phony targets
###
#######

.PHONY: cluster-results tabular-results

cluster-results: cluster-pull $(filepath-results)

tabular-results: $(filepath-results)

#######
###
#   Build target specifications
###
#######

$(filepath-results): $(filepath-parser) $(dir $(filepath-results))
	$< $(argument-demark) $(argument-outputs) > $@

$(dir $(filepath-results)):
	@mkdir -p $@

endif # IMPORT_MAKE_RESULTS
