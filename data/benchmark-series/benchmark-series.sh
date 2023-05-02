#!/bin/bash


# Command line argument derived variables.
PARAM_FILEPATH='.' # Default to current working directory
PARAM_GROUPMAX=8   # Default model parameter 'N'
PARAM_PROPERTY=FSU # Default LTL property
PARAM_TREE_VER=2   # Default version of TreeKEM protocol
PARAM_VERBIAGE=5   # Default to moderate verbosity: [0,5] -> [QUIET, ERROR, WARNS, INFOS, EXTRA, DEBUG]

# General purpose function for standardized output.
report() {
  if [[ "${PARAM_VERBIAGE}" -le 0 ]]; then return 0; fi
  local prefix=''
  case "$1" in
      tech) if [[ ${PARAM_VERBIAGE} -ge 5 ]]; then prefix='# '   ; else return 0; fi ;;
      loud) if [[ ${PARAM_VERBIAGE} -ge 4 ]]; then prefix='  '   ; else return 0; fi ;;
      warn) if [[ ${PARAM_VERBIAGE} -ge 2 ]]; then prefix='! '   ; else return 0; fi ;;
      fail) if [[ ${PARAM_VERBIAGE} -ge 1 ]]; then prefix='X '   ; else return 0; fi ;;
      *)    if [[ ${PARAM_VERBIAGE} -ge 3 ]]; then prefix='  '   ; else return 0; fi ;;
  esac
  echo -e "$prefix$2"
}


# Process the command line arguments.
parse() {
    local OPTIND
    while getopts ":xweqn:p:v:" opt; do
        case $opt in
            x) PROVIDED_VERBIAGE=4;;
            w) PROVIDED_VERBIAGE=2;;
            e) PROVIDED_VERBIAGE=1;;
            q) PROVIDED_VERBIAGE=0;;
            n) PROVIDED_GROUPMAX=$OPTARG;;
            p) PROVIDED_PROPERTY=$OPTARG;;
            v) PROVIDED_TREE_VER=$OPTARG;;
            \?) report 'fail' "Invalid option -$OPTARG" >&2 && exit 1 ;;
        esac
    done

    shift "$((OPTIND - 1))"
    # Now "$@" contains the rest of the arguments

    case "${PROVIDED_PROPERTY}" in
        FSU|PCS) PARAM_PROPERTY="${PROVIDED_PROPERTY}" ;;
        *) ;;
    esac

    # If there are one or more remaining command line arguments,
    # they are the output filepath(s)!
    if [ "$#" -ne 0 ]; then
        PARAM_FILEPATH="$1"
    fi
    
    if [[ -n "${PROVIDED_GROUPMAX+x}" ]]; then
        if ((3 <= PROVIDED_GROUPMAX && PROVIDED_GROUPMAX <= 16)); then
            PARAM_GROUPMAX="${PROVIDED_GROUPMAX}"
        fi
    fi

    if [[ -n "${PROVIDED_TREE_VER+x}" ]]; then
        if ((1 <= PROVIDED_TREE_VER && PROVIDED_TREE_VER <= 2)); then
            PARAM_TREE_VER="${PROVIDED_TREE_VER}"
        fi
    fi

    if [[ -n "${PROVIDED_VERBIAGE+x}" ]]; then
        if ((0 <= PROVIDED_VERBIAGE)); then
            PARAM_VERBIAGE="${PROVIDED_VERBIAGE}"
        fi  
    fi
    
    report 'tech' 'Collected parameters:'
    report 'tech' "PROVIDED_FILEPATH:\t'${PROVIDED_FILEPATH}'"
    report 'tech' "PROVIDED_GROUPMAX:\t'${PROVIDED_GROUPMAX}'"
    report 'tech' "PROVIDED_PROPERTY:\t'${PROVIDED_PROPERTY}'"
    report 'tech' "PROVIDED_TREE_VER:\t'${PROVIDED_TREE_VER}'"
    report 'tech' "PROVIDED_VERBIAGE:\t'${PROVIDED_VERBIAGE}'"
    report 'tech' ''
    report 'tech' 'Resulting parameters:'
    report 'tech' "PARAM_FILEPATH:\t'${PARAM_FILEPATH}'"
    report 'tech' "PARAM_GROUPMAX:\t'${PARAM_GROUPMAX}'"
    report 'tech' "PARAM_PROPERTY:\t'${PARAM_PROPERTY}'"
    report 'tech' "PARAM_TREE_VER:\t'${PARAM_TREE_VER}'"
    report 'tech' "PARAM_VERBIAGE:\t'${PARAM_VERBIAGE}'"
}


# Maximum depth to use when keeping the entire stack in memory.
#  | N |    Depth Limit | Exact (FSU) |  Exact (PCS)  |
#  |:-:|---------------:|-------------+--------------:|
#  | 3 |      1,000,000 |     289,137 |       270,670 |
#  | 4 |     22,000,000 |   5,310,869 |    21,928,268 |
#  | 5 |    550,000,000 |  22,322,498 |   521,935,069 |
#  | 6 |  1,900,000,000 |  80,411,400 | 1,886,665,850 |
#  | 7 |  2,800,000,000 |  90,295,788 | 2,739,391,389 |
#  | 8 | 25,000,000,000 | 352,029,551 |           ??? |
declare -ia DEPENDANT_MAX_STK=(
        300001
      23000001
     550000001
    1900000001
    2800000001
   25000000001    
)

# Maximum stack suffix to keep in memory before swapping prefix to/from disk.
#  | N |  Suffix Length |
#  |:-:|---------------:|
#  | 3 |        300,000 |
#  | 4 |      1,000,000 |
#  | 5 |      2,500,000 |
#  | 6 |      7,500,000 |
#  | 7 |     12,500,000 |
#  | 8 |     20,000,000 |
declare -ia DEPENDANT_MEM_STK=(
      300000
     1000000
     2500000
     7500000
    12500000
    20000000
    20000000
    20000000
    20000000
    20000000
    20000000
    20000000
    20000000
    20000000
)


# Memory to allocate for SPIN executable.
#  | N | GiB |    MiB |
#  |:-:|----:|-------:|
#  | 3 |  48 |  49152 |
#  | 4 |  56 |  57344 |
#  | 5 |  96 |  98304 |
#  | 6 | 316 | 323584 |
#  | 7 | 500 | 512000 |
#  | 8 | 950 | 972800 |
declare -ia DEPENDANT_MEM_PAN=(
     49152
     57344
     98304
    323584
    512000
    786432
    786432
    786432
    786432
    786432
    786432
    786432
    786432
    786432
)

# Memory to allocate for cluster job.
declare -ia 'DEPENDANT_MEM_JOB=( "${DEPENDANT_MEM_PAN[@]/%/+4096}" )'

# Number of bytes required to encode model state (and padded state-vector length).
#  | N | Length | Padded |
#  |:-:|-------:|-------:|
#  | 3 |     52 |    53 |
#  | 4 |     56 |    57 |
#  | 5 |     64 |    65 |
#  | 6 |     64 |    65 |
#  | 7 |     64 |    65 |
#  | 8 |     76 |    77 |
#  | 9 |     88 |    89 |
declare -ia DEPENDANT_ENC_LEN=(
    52
    56
    64
    64
    64
    68
    68
    92
    92
    92
    92
    92
    92
    92
    92
)

# Specify the size of the state vector when compiling verification executable.
declare -ia 'DEPENDANT_VEC_LEN=( "${DEPENDANT_ENC_LEN[@]/%/+1}" )'

# Space to pre-allocate for hashtable, value is power of 2; ( 2 ^ x )
#  | N | Exp |
#  |:-:|----:|
#  | 3 |  29 |
#  | 4 |  30 |
#  | 5 |  30 |
#  | 6 |  31 |
#  | 7 |  31 |
#  | 8 |  32 |
#  | 9 |  32 |
declare -ia DEPENDANT_HASHTBL=(
    29
    30
    30
    31
    31
    32
    32
    32
    32
    32
    32
    32
    32
    32
)

# 1st:
# Parse and process the commandline arguments.
parse "$@"

DEPENDANT_JOBNAME="V${PARAM_TREE_VER}-${PARAM_PROPERTY}-N${PARAM_GROUPMAX}"

N_INDEX=$((PARAM_GROUPMAX-3))

SOURCE_BASEPATH="${0%.*}"
SOURCE_BASENAME="${SOURCE_BASEPATH##*/}"
SOURCE_BASHPROG="${SOURCE_BASEPATH}.script"
SOURCE_TEMPLATE="${SOURCE_BASEPATH}.template"


OUTPUT_TEMPFILE=`mktemp -t ${SOURCE_BASENAME}-XXXXXXXXXX`
OUTPUT_FINALIZE="${SOURCE_BASEPATH}.run"

printf "SOURCE_BASENAME:\t${SOURCE_BASENAME}\n"
printf "SOURCE_BASEPATH:\t${SOURCE_BASEPATH}\n"
printf "SOURCE_BASHPROG:\t${SOURCE_BASHPROG}\n"
printf "SOURCE_TEMPLATE:\t${SOURCE_TEMPLATE}\n\n"
printf "OUTPUT_TEMPFILE:\t${OUTPUT_TEMPFILE}\n"
printf "OUTPUT_FINALIZE:\t${OUTPUT_FINALIZE}\n\n"
printf "DEPENDANT_JOBNAME:\t${DEPENDANT_JOBNAME}\n\n"

printf "PARAM_GROUPMAX:\t${PARAM_GROUPMAX}\n\n"
printf "N_INDEX:\t${N_INDEX}\n"

printf "DEPENDANT_ENC_LEN:\t${DEPENDANT_ENC_LEN[${N_INDEX}]}\n"
printf "DEPENDANT_HASHTBL:\t${DEPENDANT_HASHTBL[${N_INDEX}]}\n"
printf "DEPENDANT_MAX_STK:\t${DEPENDANT_MAX_STK[${N_INDEX}]}\n"
printf "DEPENDANT_MEM_STK:\t${DEPENDANT_MEM_STK[${N_INDEX}]}\n"
printf "DEPENDANT_MEM_PAN:\t${DEPENDANT_MEM_PAN[${N_INDEX}]}\n"
printf "DEPENDANT_MEM_JOB:\t${DEPENDANT_MEM_JOB[${N_INDEX}]}\n"
printf "DEPENDANT_VEC_LEN:\t${DEPENDANT_VEC_LEN[${N_INDEX}]}\n"
printf "DEPENDANT_JOBNAME:\t${DEPENDANT_JOBNAME}\n"
printf "PARAM_GROUPMAX:  \t${PARAM_GROUPMAX}\n"
printf "PARAM_PROPERTY:  \t${PARAM_PROPERTY}\n"
printf "PARAM_TREE_VER:  \t${PARAM_TREE_VER}\n"

echo "" | pandoc \
    --output="${OUTPUT_TEMPFILE}" \
    --read=markdown \
    --template="${SOURCE_TEMPLATE}" \
    --variable=VAR_DEPENDANT_ENC_LEN:"${DEPENDANT_ENC_LEN[${N_INDEX}]}" \
    --variable=VAR_DEPENDANT_HASHTBL:"${DEPENDANT_HASHTBL[${N_INDEX}]}" \
    --variable=VAR_DEPENDANT_MAX_STK:"${DEPENDANT_MAX_STK[${N_INDEX}]}" \
    --variable=VAR_DEPENDANT_MEM_STK:"${DEPENDANT_MEM_STK[${N_INDEX}]}" \
    --variable=VAR_DEPENDANT_MEM_PAN:"${DEPENDANT_MEM_PAN[${N_INDEX}]}" \
    --variable=VAR_DEPENDANT_MEM_JOB:"${DEPENDANT_MEM_JOB[${N_INDEX}]}" \
    --variable=VAR_DEPENDANT_VEC_LEN:"${DEPENDANT_VEC_LEN[${N_INDEX}]}" \
    --variable=VAR_DEPENDANT_JOBNAME:"${DEPENDANT_JOBNAME}" \
    --variable=VAR_GROUPMAX:"${PARAM_GROUPMAX}" \
    --variable=VAR_PROPERTY:"${PARAM_PROPERTY}" \
    --variable=VAR_TREE_VER:"${PARAM_TREE_VER}" \
    --write=plain

cat "${OUTPUT_TEMPFILE}" "${SOURCE_BASHPROG}" > "${OUTPUT_FINALIZE}"
rm  "${OUTPUT_TEMPFILE}"

