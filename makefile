.ONESHELL:

SHELL ::= /bin/bash
EMPTY ::=

encoding-basename    ::= pan
extension-makefile   ::= mk
extension-promela    ::= pml

dir-binaries         ::= ./bin
dir-source-code      ::= ./src
dir-output-encoding  ::= $(dir-source-code)/$(encoding-basename)
dir-make-definitions ::= $(dir-source-code)/$(extension-makefile)
dir-protocol-model   ::= $(dir-source-code)/$(extension-promela)

dir-add-these ::= $(wildcard $(dir-make-definitions)/*.$(extension-makefile))

-include $(wildcard $(dir-make-definitions)/*.$(extension-makefile))

all: transpile
	@echo "Finished at top"
