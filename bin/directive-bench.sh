#!/bin/bash

# > Nodes & CPUs:
#PBS -l nodes=1:ppn=8
#
# > Memory:
#PBS -l mem=65536mb
#
# > Estimated runtime:
#PBS -l walltime=30-00:00:00
#
# > Email:
#PBS -m abe
#PBS -M cluster-notifications@recursion.ninja
#
# > Job name:
#PBS -N CGKA-TreeKEM-Benchmarks
#
# > Queue:
#PBS -q batch-amd
#
# > Shell:
#PBS -S /bin/bash
#
# > Inherit environment variables
#PBS -V
#
VECLEN=72

DIRECTIVE_DEFAULTS=(
    'MEMLIM=63488'
    'NOBOUNDCHECK'
    'NOFAIR'
)

DIRECTIVE_ELEMENTS=(
    'COLLAPSE'
    'HC'
    "MA=${VECLEN}"
    'SPACE'
    "VECTORSZ=${VECLEN}"
)

FLAG_DEFAULTS=("${DIRECTIVE_DEFAULTS[@]/#/-D}")
FLAG_ELEMENTS=("${DIRECTIVE_ELEMENTS[@]/#/-D}")
FLAG_SPECTRUM=()

count=${#FLAG_ELEMENTS[@]}
bound=$((1 << ${count}))
i=0
while [ ${i} -lt ${bound} ]
do
    subset=""
    j=0
    while [ ${j} -lt ${count} ]
    do
        if [ $(((1 << ${j}) & ${i})) -gt 0 ]
        then
            subset+="${FLAG_ELEMENTS[$j]} "
        fi
        j=$((${j} + 1))
    done
    FLAG_SPECTRUM+=("${subset}")
    i=$((${i} + 1))
done

if [ -z ${SLURM_ARRAY_TASK_ID+x} ]; then
    echo "No specified 'SLURM_ARRAY_TASK_ID'"
    exit 2
fi

FLAG_ELECTION="${FLAG_SPECTRUM[$SLURM_ARRAY_TASK_ID]}"
NAME_BINARY="CGKA-Bench-${SLURM_ARRAY_TASK_ID}"

if [[ -z "${FLAG_ELECTION}" ]]; then
    FLAG_RENDERED="{} (Empty Set)"
else
    FLAG_RENDERED="{ $(echo -e "${FLAG_ELECTION}" | sed -e 's/[[:space:]]*$//' -e 's/[[:space:]]\+/, /g') }"
fi

echo -e "Benchmarking selected directive set:\n\t${FLAG_RENDERED}"

gcc \
    ${FLAG_DEFAULTS[@]} \
    ${FLAG_ELECTION} \
    -O3 \
    -o "${NAME_BINARY}" \
    pan.h pan.c

chmod +x "${NAME_BINARY}"

./"${NAME_BINARY}" -a -A -v -x

sstat --allsteps --format=AveCPU,AvePages,AveRSS,AveVMSize,JobID --jobs ${SLURM_JOBID} --parsable

#/usr/bin/time -f "DIRECTIVE: ${FLAG_ELECTION}\n\tElapsed time: %es\n\tMemory usage: %M KB\n\tCPU usage: %P\n\n${FLAG_ELECTION}\t%e\t%M\n\n" "./${NAME_BINARY}" -a -A -v -x

# 
