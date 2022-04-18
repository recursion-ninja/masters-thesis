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
SPACE ::= $(EMPTY) $(EMPTY)

endif # IMPORT_MAKE_ENVIRONMENT

ifndef IMPORT_MAKE_CLUSTER
IMPORT_MAKE_CLUSTER ::= 1

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

basename-dependancies ::= compile constants transpile
filename-dependancies ::= $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-dependancies ::= $(abspath $(addprefix $(dir-make-definitions),$(filename-dependancies)))

-include $(filepath-dependancies)

#######
###
#   Variables for CLUSTER
###
#######

# Distribution to be moved to cluster
filename-bundle ::= $(infostr)
filepath-bundle ::= $(abspath $(addprefix $(dir-source-code),$(filename-bundle)))

# Distribution's PBS script file
prefname-pbs          ::= pbs.
prefpath-pbs          ::= $(abspath $(dir-pbs-script-parts)/$(prefname-pbs))
filepath-pbs-body     ::= $(prefpath-pbs)script
filepath-pbs-config   ::= $(abspath $(shell mktemp -d -t $(prefname-pbs)-XXXXXXXXXX)/config)
filepath-pbs-defaults ::= $(prefpath-pbs)defaults
filepath-pbs-template ::= $(prefpath-pbs)template

basename-makefile-parts  ::= compile constants transpile
filename-makefile-parts  ::= $(addsuffix .$(extension-makefile),$(basename-dependancies))
filepath-makefile-parts  ::= $(abspath $(addprefix $(dir-make-definitions),$(filename-makefile-parts)))

filename-bundle-code     ::= $(notdir $(sources-verifier))
filepath-bundle-code     ::= $(abspath $(addprefix $(filepath-bundle)/,$(filename-bundle-code)))
filename-bundle-pbs      ::= $(filename-bundle)-pbs.sh
filepath-bundle-pbs      ::= $(abspath $(filepath-bundle)/$(filename-bundle-pbs))
filepath-bundle-makefile ::= $(abspath $(filepath-bundle)/makefile)
filepath-bundle-mkparts  ::= $(abspath $(addprefix $(filepath-bundle),$(filename-makefile-parts)))

filepath-bundle-complete ::=    \
    $(filepath-bundle-code)     \
    $(filepath-bundle-makefile) \
    $(filepath-bundle-mkparts)  \
    $(filepath-bundle-pbs)

local-code   := $(local-dir)/$(cluster-dir-remote)
local-pbs    := $(local-dir)/$(cluster-pbs)



cluster-dir-prefix := spin-src-v
cluster-dir-format := $(cluster-dir-prefix)*
cluster-dir-remote := $(cluster-dir-prefix)$(version)

cluster-pbs-suffix := -
cluster-pbs-format := *$(cluster-pbs-suffix).*

cluster-host := ${CLUSTER_HOST}
cluster-user := ${CLUSTER_USER}
cluster-pass := ${CLUSTER_PASS}
cluster-auth := $(cluster-user)@$(cluster-host)
cluster-pbs  := $(process)$(cluster-pbs-suffix)

cluster-log-pattern ::= $(infostr-pattern)

#######
###
#   Custom function definitions for CLUSTER
###
#######

define scp-with
	@sshpass -p $(cluster-pass) scp -r $(1) $(2) && echo "\tFROM: $(1)\n\tTO:   $(2)\n"
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
	rm -fr $(filepath-bundle)

installdirs:: $(filepath-bundle)

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

cluster-connect: ask-password
	$(call ssh-with)

cluster-pull: ask-password
	@$(call scp-with,'$(cluster-auth):./{$(example-dir),$(logging-dir)}',$(dir-logging))

cluster-push: $(filepath-bundle-complete) ask-password
	@echo "Transfering:"
	@$(call scp-with,"$(filepath-bundle)","$(cluster-auth):./")

cluster-verify:
	$(eval cluster-working-directory ::= '$$$${HOME}/$(filename-bundle)')
	$(eval cluster-filepath-script   ::= '$$$${HOME}/$(filename-bundle)/$(filename-bundle-pbs)')
	$(call ssh-with,'qsub -wd $(cluster-working-directory) $(cluster-filepath-script)')

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

$(filepath-pbs-config): $(filepath-pbs-defaults) $(filepath-pbs-template)
	@echo "" | pandoc \
	  --metadata-file=$(filepath-pbs-defaults) \
	  --output=$@ \
	  --read=markdown \
	  --template=$(filepath-pbs-template) \
	  --variable=name:CGKA \
	  --variable=version:$(infostr-suffix-variable) \
	  --write=plain


endif # IMPORT_MAKE_CLUSTER


# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# 
# default-param-C := 4
# default-param-N := 4
# default-param-T := 4
# default-process := CGKA-TreeKEM
# default-version := 1.0
# 
# ifndef C
# C := $(default-param-C)
# endif
# ifndef N
# N := $(default-param-N)
# endif
# ifndef T
# T := $(default-param-T)
# endif
# ifndef process
# process := $(default-process)
# endif
# ifndef version
# version := $(default-version)
# endif
# 
# #model-name  = TreeKEM
# model-name := Oracles
# model-in-C := pan.c pan.h
# model-code := pan.b $(model-in-C) pan.m pan.p pan.t
# model-pans := $(shell tr ' ' ',' <<<"./{$(model-code)}")
# model-file := ../$(model-name).promela
# 
# example-dir  := trails
# logging-des  := ../../log
# logging-dir  := $(cluster-dir-format)/$(cluster-pbs-format)
# 
# bits_required = calculate_bits_required() { \
#   bits_floored=$$(echo "scale=3; l($$1)/l(2)" | bc -l | cut -f1 -d"."); \
#   echo "$$bits_floored"; \
#   bits_result=$$((bits_floored+1)); \
#   $(eval $$2 := $$(shell echo $$bits_result)); \
# }
# 
# ifneq (,$(findstring n,$(MAKEFLAGS)))
# bits_required =: bits_required
# endif
