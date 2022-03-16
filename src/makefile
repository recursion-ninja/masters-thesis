SHELL=/bin/bash

#component  = TreeKEM
component  = Oracles
extension  = promela
source     = $(component).$(extension)
executable = $(component).analysis
trail      = $(source).trail
backups    = trails
dot-output = counterexample

# Default build target
all: execute-pan inspect-pan

$(executable): $(source)
	spin -a $(component)*.$(extension)
	cat <(echo "#include <stdio.h>") pan.h > pan.h.temp
	mv pan.h.temp pan.h
	gcc -O3 -DVECTORSZ=65536 -o $(executable) pan.h pan.c

execute-pan: $(executable)
	mv --backup=t $(trail) $(backups)/$(trail) 2>/dev/null || true
	./$(executable) -a

inspect-pan:
ifneq (,$(wildcard $(trail)))
	spin -t $(source)
endif

clean:
	rm -f $(executable) pan.* *~


image: $(executable)
	./$(executable) -a -D > $(dot-output).dot
	dot -Tpng -Gdpi=600 $(dot-output).dot > $(dot-output).png
