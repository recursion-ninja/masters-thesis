SHELL=/bin/bash

#component  = TreeKEM
component  = Oracles
extension  = promela
source     = $(component).$(extension)
executable = $(component).analysis
trail      = $(source).trail
backups    = trails

# Default build target
all: compile-pan execute-pan inspect-pan

compile-pan: $(source)
	spin -a $(component)*.$(extension)
	cat <(echo "#include <stdio.h>") pan.h > pan.h.temp
	mv pan.h.temp pan.h
	gcc -O3 -DVECTORSZ=65536 -o $(executable) pan.h pan.c

execute-pan: $(executable)
	mv --backup=t $(trail) $(backups)/$(trail) 2>/dev/null || true
	./$(executable) -a -i

inspect-pan: $(trail)
	spin -t $(source)

clean:
	rm -f $(executable) pan.* *~
