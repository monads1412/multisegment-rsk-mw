#!/usr/bin/env bash

# Usage:
#   bash run_bounded_tests.sh [MAX_ENDPOINT_BOUND] [MAX_SEGMENTS]
#
# Example:
#   bash run_bounded_tests.sh 3 2
#
# Runs EndpointBound = 1, 2, ..., MAX_ENDPOINT_BOUND while keeping
# MaxSegments fixed. It does not modify FormalizedCorollary.tla or Utils.tla.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR" || exit 2

MAX_ENDPOINT_BOUND="${1:-2}"
MAX_SEGMENTS="${2:-2}"
TLA2TOOLS_JAR="${TLA2TOOLS_JAR:-$SCRIPT_DIR/tla2tools.jar}"

if ! [[ "$MAX_ENDPOINT_BOUND" =~ ^[1-9][0-9]*$ ]]; then
    echo "MAX_ENDPOINT_BOUND must be a positive integer."
    exit 2
fi

if ! [[ "$MAX_SEGMENTS" =~ ^[1-9][0-9]*$ ]]; then
    echo "MAX_SEGMENTS must be a positive integer."
    exit 2
fi

if [[ ! -f "$TLA2TOOLS_JAR" ]]; then
    echo "Could not find tla2tools.jar at: $TLA2TOOLS_JAR"
    echo "Put tla2tools.jar beside this script, or set TLA2TOOLS_JAR."
    exit 2
fi

if [[ ! -f "$SCRIPT_DIR/FormalizedCorollary.tla" ]]; then
    echo "Could not find FormalizedCorollary.tla beside this script."
    exit 2
fi

if [[ ! -f "$SCRIPT_DIR/Utils.tla" ]]; then
    echo "Could not find Utils.tla beside this script."
    exit 2
fi

mkdir -p "$SCRIPT_DIR/bounded-test-logs"
failed=0

for ((B=1; B<=MAX_ENDPOINT_BOUND; B++)); do
    segment_count=$(( (2*B + 1) * (B + 1) ))

    case_count=0
    power=1
    for ((num_segments=1; num_segments<=MAX_SEGMENTS; num_segments++)); do
        power=$(( power * segment_count ))
        case_count=$(( case_count + power ))
    done

    cfg="$SCRIPT_DIR/bounded-test-logs/bound_${B}_len_${MAX_SEGMENTS}.cfg"
    log="$SCRIPT_DIR/bounded-test-logs/bound_${B}_len_${MAX_SEGMENTS}.log"

    cat > "$cfg" <<CFG
CONSTANTS
    EndpointBound = $B
    MaxSegments = $MAX_SEGMENTS

SPECIFICATION Spec

INVARIANTS
    BoundedUniverseCheck
    Lemma1Check
    Corollary1Check
    Corollary2Check
    Corollary3Check
CFG

    echo
    echo "============================================================"
    echo "EndpointBound = $B"
    echo "MaxSegments   = $MAX_SEGMENTS"
    echo "Input segments = $segment_count"
    echo "Input multisegment sequences = $case_count"
    echo "============================================================"

    java -XX:+UseParallelGC \
        -cp "$TLA2TOOLS_JAR" \
        tlc2.TLC \
        -config "$cfg" \
        BoundedTests 2>&1 | tee "$log"

    status=${PIPESTATUS[0]}

    if [[ $status -eq 0 ]]; then
        echo "PASS: EndpointBound=$B, MaxSegments=$MAX_SEGMENTS"
    else
        echo "FAIL: EndpointBound=$B, MaxSegments=$MAX_SEGMENTS"
        echo "See: $log"
        failed=1
        break
    fi
done

exit $failed
