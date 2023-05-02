#!/bin/bash

for version in 1 2
do
    for property in FSU PCS
    do
        for N in 16
        do
            make clean-encoding-files
            make benchmark-series version=${version} LTL=${property} N=${N}
            printf "Bundled:\t v%d %s N=%d\n" "${version}" "${property}" "${N}"
        done
    done
done
printf "\tDone!\n"
