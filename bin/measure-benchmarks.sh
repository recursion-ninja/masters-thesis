#!/bin/bash

for version in 1 2
do
    for property in FSU PCS
    do
        for N in 3 4 5 6 7 8
        do
            cd "CGKA-TreeKEM-v${version}-${property}-N00${N}"
            sbatch --array=0-7 benchmark-series.run
            cd ../
        done
    done
done
printf "\tDone!\n"
