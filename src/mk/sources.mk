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

ifndef IMPORT_MAKE_SOURCES
IMPORT_MAKE_SOURCES := 1

#######
###
#   Conditionl Redefinitions
###
#######

basename-encoding    ?= pan
extension-promela    ?= pml 
dir-output-encoding  ?= ./
dir-protocol-model   ?= ./

#######
###
#   Variables for SOURCES
###
#######

model-specification       := Model-Specification
filename-modeling-spec    := $(model-specification).$(extension-promela)
filename-modeling-code    := $(wildcard $(dir-protocol-model)*$(extension-promela))
filepath-modeling-spec    := $(abspath $(addprefix $(dir-protocol-model),$(filename-modeling-spec)))
filepath-modeling-code    := $(abspath $(filename-modeling-code))

extensions-encoding-in-C  := c h
extensions-encoding-code  := $(sort b m p t $(extensions-encoding-in-C))

filename-encoding-in-C    := $(addprefix $(basename-encoding).,$(extensions-encoding-in-C))
filename-encoding-code    := $(addprefix $(basename-encoding).,$(extensions-encoding-code))
filepath-encoding-in-C    := $(sort $(abspath $(addprefix $(dir-output-encoding),$(filename-encoding-in-C))))
filepath-encoding-code    := $(sort $(abspath $(addprefix $(dir-output-encoding),$(filename-encoding-code))))
filepath-encoding-pattern := $(dir-output-encoding)$(basename-encoding).*

$(info $(filepath-encoding-pattern))

#######
###
#   Standard targets
###
#######

.PHONY: all

all:: $(filepath-encoding-code)

endif # IMPORT_MAKE_SOURCES
