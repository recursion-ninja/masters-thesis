SHELL=/bin/bash

#######
###
#   Constants
###
#######

process-default := TreeKEM-CGKA
version-default := 2.3

ifndef process
process := $(process-default)
endif
ifndef version
version := $(version-default)
endif

#model-name  = TreeKEM
model-name := Oracles
model-in-C := pan.c pan.h
model-code := pan.b $(model-in-C) pan.m pan.p pan.t
model-pans := $(shell tr ' ' ',' <<<"./{$(model-code)}")
model-file := ../$(model-name).promela

cluster-dir-prefix := spin-src-v
cluster-dir-format := $(cluster-dir-prefix)*
cluster-dir-remote := $(cluster-dir-prefix)$(version)

cluster-pbs-suffix := -pbs.sh
cluster-pbs-format := *$(cluster-pbs-suffix).*

cluster-host := ${CLUSTER_HOST}
cluster-user := ${CLUSTER_USER}
cluster-auth := $(cluster-user)@$(cluster-host)
cluster-pass :=
cluster-pbs  := $(process)$(cluster-pbs-suffix)


pbs-dir      := pbs
pbs-prefix   := $(pbs-dir)/pbs.
pbs-body     := $(pbs-prefix)script
pbs-config   := $(pbs-prefix)config
pbs-defaults := $(pbs-prefix)defaults
pbs-makefile := $(pbs-dir)/makefile
pbs-template := $(pbs-prefix)template

local-dir  := remote
local-code := $(local-dir)/$(cluster-dir-remote)
local-pbs  := $(local-dir)/$(cluster-pbs)

retrieve-des = ../../log
retrieve-dir = $(cluster-dir-format)/$(cluster-pbs-format)

#######
###
#   Phony targets
###
#######

all: verification

ask_password:
ifeq ($(cluster-pass),)
	@$(eval cluster-pass=$(shell stty -echo; read -p "Password for $(cluster-auth): " secret; stty echo; echo $$secret))
	@echo ""
endif

clean:
	rm -fr **/*~ **/*# $(model-code) $(cluster-dir-format) $(pbs-config)

cluster-connect: ask_password
	@sshpass -p $(cluster-pass) ssh $(cluster-auth)

cluster-pull: ask_password
	sshpass -p $(cluster-pass) scp '$(cluster-auth):./$(retrieve-dir)' $(retrieve-des)

cluster-push: $(local-pbs) $(local-code) ask_password
	@echo "Transfering:"
	@$(MAKE) --no-print-directory scp-with pass=$(cluster-pass) src="$(local-pbs)"
	@$(MAKE) --no-print-directory scp-with pass=$(cluster-pass) src="$(local-code)"
	@rm -rf $(local-dir)

scp-with:
	@sshpass -p $(pass) scp -r $(src) $(cluster-auth):./ && echo -en "\t$(src)\n"

transpile: $(model-code)

#######
###
#   Build target specifications
###
#######

$(local-code): $(local-dir) $(model-code) $(model-file) $(pbs-makefile)
	@mkdir -p $(local-code)
	@cp $(pbs-makefile) $(local-code)
	@cp $(model-file)   $(local-code)
	@cp $(model-pans)   $(local-code)
	@echo -e "Bundled codes\t$(local-code)"

$(local-dir):
	@mkdir $(local-dir)

$(local-pbs): $(local-dir) $(pbs-body) $(pbs-config)
	@cat   $(pbs-config) $(pbs-body) > $(local-pbs)
	@rm -f $(pbs-config)
	@echo -e "Interpolated\t$(local-pbs)"

$(model-code): $(model-file)
	spin -a $(model-file)
	cat <(echo "#include <stdio.h>") pan.h > pan.h.temp
	mv pan.h.temp pan.h

$(pbs-config): $(pbs-defaults) $(pbs-template)
	@echo "" | pandoc \
	  --metadata-file=$(pbs-defaults) \
	  --output=$(pbs-config) \
	  --read=markdown \
	  --template=$(pbs-template) \
	  --variable=name:$(process) \
	  --variable=version:$(version) \
	  --write=plain

.PHONY: all ask_password clean cluster-connect cluster-push cluster-pull scp-with transpile
