#!/usr/bin/env bash

# Comprehensive random testing for the two implementations.
#
# Usage:
#   bash run_random_tests.sh \
#       [SAMPLE_COUNT] [ENDPOINT_BOUND] [MAX_DISTINCT_SEGMENTS] \
#       [MAX_MULTIPLICITY] [MAX_TOTAL_CARDINALITY] [SEED] [MODE]
#
# MODE: sequence | bag | both
#
# Example (recommended first sequence stress test):
#   bash run_random_tests.sh 2000 20 4 2 5 12345 sequence
#
# Example (same 500 mathematical multisegments in both representations):
#   bash run_random_tests.sh 500 20 4 2 5 12345 both
#
# Optional:
#   COUNT_COROLLARY_CASES=1 bash run_random_tests.sh ...
# runs an additional diagnostic TLC pass whose initial states are exactly
# the sampled multisegments satisfying min(M) < min(l(M)).

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR" || exit 2

SAMPLE_COUNT="${1:-2000}"
ENDPOINT_BOUND="${2:-20}"
MAX_DISTINCT_SEGMENTS="${3:-4}"
MAX_MULTIPLICITY="${4:-2}"
MAX_TOTAL_CARDINALITY="${5:-5}"
SEED="${6:-12345}"
MODE="${7:-sequence}"
COUNT_COROLLARY_CASES="${COUNT_COROLLARY_CASES:-0}"

TLA2TOOLS_JAR="${TLA2TOOLS_JAR:-$SCRIPT_DIR/tla2tools.jar}"

for pair in \
    "SAMPLE_COUNT:$SAMPLE_COUNT" \
    "ENDPOINT_BOUND:$ENDPOINT_BOUND" \
    "MAX_DISTINCT_SEGMENTS:$MAX_DISTINCT_SEGMENTS" \
    "MAX_MULTIPLICITY:$MAX_MULTIPLICITY" \
    "MAX_TOTAL_CARDINALITY:$MAX_TOTAL_CARDINALITY"
do
    name="${pair%%:*}"
    value="${pair#*:}"
    if ! [[ "$value" =~ ^[1-9][0-9]*$ ]]; then
        echo "$name must be a positive integer."
        exit 2
    fi
done

if ! [[ "$SEED" =~ ^-?[0-9]+$ ]]; then
    echo "SEED must be an integer."
    exit 2
fi

case "$MODE" in
    sequence|bag|both) ;;
    *)
        echo "MODE must be one of: sequence, bag, both"
        exit 2
        ;;
esac

if [[ "$COUNT_COROLLARY_CASES" != "0" && "$COUNT_COROLLARY_CASES" != "1" ]]; then
    echo "COUNT_COROLLARY_CASES must be 0 or 1."
    exit 2
fi

if [[ ! -f "$TLA2TOOLS_JAR" ]]; then
    echo "Could not find tla2tools.jar at: $TLA2TOOLS_JAR"
    echo "Put tla2tools.jar beside this script, or set TLA2TOOLS_JAR."
    exit 2
fi

if [[ ! -f "$SCRIPT_DIR/Utils.tla" ]]; then
    echo "Could not find Utils.tla beside this script."
    exit 2
fi

if [[ "$MODE" == "sequence" || "$MODE" == "both" ]]; then
    if [[ ! -f "$SCRIPT_DIR/FormalizedCorollary.tla" ]]; then
        echo "Could not find FormalizedCorollary.tla beside this script."
        exit 2
    fi
fi

if [[ "$MODE" == "bag" || "$MODE" == "both" ]]; then
    if [[ ! -f "$SCRIPT_DIR/BagFormalization.tla" ]]; then
        echo "Could not find BagFormalization.tla beside this script."
        exit 2
    fi
fi

if ! command -v python3 >/dev/null 2>&1; then
    echo "python3 is required to generate the random sample."
    exit 2
fi

python3 "$SCRIPT_DIR/generate_random_tests.py" \
    "$SAMPLE_COUNT" \
    "$ENDPOINT_BOUND" \
    "$MAX_DISTINCT_SEGMENTS" \
    "$MAX_MULTIPLICITY" \
    "$MAX_TOTAL_CARDINALITY" \
    "$SEED" || exit 2

mkdir -p "$SCRIPT_DIR/random-test-logs"

printf '\n============================================================\n'
echo "Comprehensive randomized test"
echo "Samples                     = $SAMPLE_COUNT"
echo "Endpoint range              = -$ENDPOINT_BOUND..$ENDPOINT_BOUND"
echo "Distinct segments           = 1..$MAX_DISTINCT_SEGMENTS"
echo "Multiplicity per segment    = 1..$MAX_MULTIPLICITY"
echo "Total cardinality cap       = $MAX_TOTAL_CARDINALITY"
echo "Seed                        = $SEED"
echo "Mode                        = $MODE"
echo "============================================================"

run_tlc() {
    local module="$1"
    local cfg="$2"
    local label="$3"
    local suffix="$4"
    local log="$SCRIPT_DIR/random-test-logs/${label}_n${SAMPLE_COUNT}_b${ENDPOINT_BOUND}_d${MAX_DISTINCT_SEGMENTS}_m${MAX_MULTIPLICITY}_t${MAX_TOTAL_CARDINALITY}_seed${SEED}_${suffix}.log"

    printf '\n------------------------------------------------------------\n'
    echo "$label"
    echo "------------------------------------------------------------"

    java -XX:+UseParallelGC \
        -cp "$TLA2TOOLS_JAR" \
        tlc2.TLC \
        -config "$SCRIPT_DIR/$cfg" \
        "$module" 2>&1 | tee "$log"

    local status=${PIPESTATUS[0]}
    if [[ $status -ne 0 ]]; then
        echo "FAIL: $label"
        echo "See: $log"
        return "$status"
    fi

    echo "PASS: $label"
    return 0
}

if [[ "$MODE" == "sequence" || "$MODE" == "both" ]]; then
    run_tlc "RandomSequenceTests" "RandomSequenceTests.cfg" \
        "sequence" "full" || exit $?

    if [[ "$COUNT_COROLLARY_CASES" == "1" ]]; then
        echo
        echo "Diagnostic pass: the distinct initial-state count below is the"
        echo "number of sampled SEQUENCE inputs satisfying min(M) < min(l(M))."
        run_tlc "RandomSequenceTests" "RandomSequenceCorollaryCases.cfg" \
            "sequence" "corollary_cases" || exit $?
    fi
fi

if [[ "$MODE" == "bag" || "$MODE" == "both" ]]; then
    run_tlc "RandomBagTests" "RandomBagTests.cfg" \
        "bag" "full" || exit $?

    if [[ "$COUNT_COROLLARY_CASES" == "1" ]]; then
        echo
        echo "Diagnostic pass: the distinct initial-state count below is the"
        echo "number of sampled BAG inputs satisfying min(M) < min(l(M))."
        run_tlc "RandomBagTests" "RandomBagCorollaryCases.cfg" \
            "bag" "corollary_cases" || exit $?
    fi
fi

printf '\n============================================================\n'
echo "ALL REQUESTED RANDOM TESTS PASSED"
echo "Seed = $SEED"
echo "============================================================"
