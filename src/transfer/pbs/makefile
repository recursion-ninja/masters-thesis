SHELL=/bin/bash

#component  = TreeKEM
component  = Oracles
source     = $(component).promela
executable = $(component).analysis
model-code = pan.b pan.c pan.h pan.m pan.p pan.t
model-in-C = pan.c pan.h
trail      = $(source).trail
backup-dir = trails

dot-output = $(image-name).dot
image-file = $(image-name).png
image-name = counterexample

directives = $(opt-memory) \
    $(opt-thread) \
    $(opt-timing) \

opt-memory = -DCOLLAPSE \
    -DVECTORSZ=65536 #\
    -DMA=256


# 256 GB RAM
# 32 Cores
opt-thread = #-DMEMLIM=262144 \
    -DNCORE=32

opt-timing = #-DNOBOUNDCHECK -DSAFETY

# Default build target
all: verification

compile:   $(executable)
analyze:   verification
inspect:   verification inspection

$(executable): $(model-code) $(source)
	gcc -O3 $(directives) -o $(executable) $(model-in-C)

verification: $(executable) backup
	time ./$(executable) -a

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

.PHONY: all analyze backup clean compile verification
