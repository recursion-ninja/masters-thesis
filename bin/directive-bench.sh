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
MINDFA=80
VECLEN=80

# 120 GiB = 122880 MiB
DIRECTIVE_DEFAULTS=(
    'JOINPROCS'
    'MEMLIM=122880'
    'MURMUR'
    'NOBOUNDCHECK'
    'NOFIX'
    'SEPQS'
    'SFH'
)

#SLURM_ARRAY_TASK_ID=0
#DIRECTIVE_ELEMENTS=(
#)

#    'JOINPROCS'
#    'MURMUR'
#    'NOBOUNDCHECK'
#    'NOFIX'
#    'SEPQS'
#    'SFH'

#DIRECTIVE_ELEMENTS=(
#    'COLLAPSE'
#    'JOINPROCS'
#    'MURMUR'
#    'NOBOUNDCHECK'
#    'NOFAIR'
#    'NOFIX'
#    'NOVSZ'
#    'SEPQS'
#    'SFH'
#)
    
#    'SAFETY'

DIRECTIVE_STRATEGY_1=(
    'HC4'
)

DIRECTIVE_STRATEGY_2=(
    "COLLAPSE"
    "MA=${MINDFA}"
)

DIRECTIVE_ELEMENTS=(
    'NOFAIR'
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
        directive="${FLAG_ELEMENTS[$j]} "
        if [ $(((1 << ${j}) & ${i})) -gt 0 ]
        then
            subset+="${directive}"
        else
            number=${#directive}
            subset+=`printf '%*s' "${#directive}"`
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

NAME_BINARY="CGKA-Bench-${SLURM_ARRAY_TASK_ID}"

if [[ ${SLURM_ARRAY_TASK_ID} -ge ${bound} ]]; then
    FLAG_SELECTION=$((SLURM_ARRAY_TASK_ID-bound))
    FLAG_STRATEGY="${DIRECTIVE_STRATEGY_1[@]/#/-D}"
else
    FLAG_SELECTION=${SLURM_ARRAY_TASK_ID}
    FLAG_STRATEGY="${DIRECTIVE_STRATEGY_2[@]/#/-D}"
fi

echo "Strategy: ${FLAG_STRATEGY}"

FLAG_ELECTION="${FLAG_STRATEGY[@]} ${FLAG_SPECTRUM[$FLAG_SELECTION]}"

if [[ -z "${FLAG_ELECTION}" ]]; then
    FLAG_RENDERED="{} (Empty Set)"
else
    FLAG_RENDERED="{ $(echo -e "${FLAG_ELECTION}") }"
fi

echo -e "Benchmarking selected directive set:\n\t${FLAG_RENDERED}"

gcc \
    ${FLAG_DEFAULTS[@]} \
    ${FLAG_ELECTION} \
    -O3 \
    -o "${NAME_BINARY}" \
    pan.h pan.c

chmod +x "${NAME_BINARY}"

./"${NAME_BINARY}" -a -A -N HLT -v -w28 -x

sstat --allsteps --format=AveCPU,AvePages,AveRSS,AveVMSize,JobID --jobs ${SLURM_JOBID} --parsable

#/usr/bin/time -f "DIRECTIVE: ${FLAG_ELECTION}\n\tElapsed time: %es\n\tMemory usage: %M KB\n\tCPU usage: %P\n\n${FLAG_ELECTION}\t%e\t%M\n\n" "./${NAME_BINARY}" -a -A -v -x

# 
