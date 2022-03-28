SHELL=/bin/bash

#component  = TreeKEM
component  = Oracles
extension  = promela
source     = $(component).$(extension)
executable = $(component).analysis
model-code = pan.b pan.c pan.h pan.m pan.p pan.t
model-in-C = pan.c pan.h
trail      = $(source).trail
backup-dir = trails
dot-output = $(image-name).dot
image-file = $(image-name).png
image-name = counterexample
#directives = -DCOLLAPSE -DNIBIS -DVECTORSZ=65536
directives = -DVECTORSZ=65536

log-decree = 1> $(log-to-out) 2> $(log-to-err)
log-prefix = verification
log-to-out = $(log-prefix).log
log-to-err = $(log-prefix).err


# Default build target
all: verification

transpile: $(model-code)
compile:   $(executable)
analyze:   verification
inspect:   verification inspection
picture:   $(image-file)

$(model-code): $(source)
	spin -a $(source)
	cat <(echo "#include <stdio.h>") pan.h > pan.h.temp
	mv pan.h.temp pan.h

$(executable): $(model-code)
	gcc -O3 $(directives) -o $(executable) $(model-in-C)

verification: $(executable) backup
	time ./$(executable) -a $(log-decree)

inspection:
ifneq (,$(wildcard $(trail)))
	spin -t $(source)
endif

$(dot-output): $(executable) backup
	./$(executable) -a -D > $(dot-output)

$(image-file): $(dot-output)
	dot -Tpng -Gdpi=600 $(dot-output) > $(image-file)

$(backup-dir):
	mkdir -p $(backup-dir)

backup: $(backup-dir)
	mv --backup=t $(trail) $(backup-dir)/$(trail) 2>/dev/null || true

clean:
	rm -f *~ *# $(executable) $(model-code) $(log-to-out) $(log-to-err)

.PHONY: all analyze backup clean compile verification image inspect inspection picture transpile
