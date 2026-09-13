#!/usr/bin/env bash

# Usage:
#   bash run_bounded_bag_tests.sh [MAX_ENDPOINT_BOUND] [MAX_SEGMENTS]
#
# Example:
#   bash run_bounded_bag_tests.sh 2 3
#
# Runs EndpointBound = 1, 2, ..., MAX_ENDPOINT_BOUND while keeping
# MaxSegments fixed.  MaxSegments is BAG CARDINALITY: repetitions count.
#
# This script does not modify BagFormalization.tla or Utils.tla.

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

if [[ ! -f "$SCRIPT_DIR/BagFormalization.tla" ]]; then
    echo "Could not find BagFormalization.tla beside this script."
    exit 2
fi

if [[ ! -f "$SCRIPT_DIR/Utils.tla" ]]; then
    echo "Could not find Utils.tla beside this script."
    exit 2
fi

# Integer binomial coefficient n choose k.
binom() {
    local n="$1"
    local k="$2"
    local result=1
    local i

    if (( k < 0 || k > n )); then
        echo 0
        return
    fi
    if (( k > n - k )); then
        k=$((n - k))
    fi
    for ((i=1; i<=k; i++)); do
        result=$(( result * (n - k + i) / i ))
    done
    echo "$result"
}

mkdir -p "$SCRIPT_DIR/bounded-bag-test-logs"
failed=0

for ((B=1; B<=MAX_ENDPOINT_BOUND; B++)); do
    # Number of legal [a,b] records with a,b in -B..B and a <= b.
    segment_count=$(( (2*B + 1) * (B + 1) ))

    # The TLA+ universe is generated from all sequences of lengths 1..k.
    sequence_count=0
    power=1
    for ((num_segments=1; num_segments<=MAX_SEGMENTS; num_segments++)); do
        power=$(( power * segment_count ))
        sequence_count=$(( sequence_count + power ))
    done

    # Distinct bags of total cardinality 1..k over n segment types:
    # C(n+k, k) - 1.
    distinct_bag_count=$(( $(binom $((segment_count + MAX_SEGMENTS)) "$MAX_SEGMENTS") - 1 ))

    cfg="$SCRIPT_DIR/bounded-bag-test-logs/bound_${B}_card_${MAX_SEGMENTS}.cfg"
    log="$SCRIPT_DIR/bounded-bag-test-logs/bound_${B}_card_${MAX_SEGMENTS}.log"

    cat > "$cfg" <<CFG
CONSTANTS
    EndpointBound = $B
    MaxSegments = $MAX_SEGMENTS

SPECIFICATION Spec

INVARIANTS
    BoundedUniverseCheck
    StandardOrderCheck
    GlobalIndexCoverageCheck
    AdmissibleEnumerationCheck
    Lemma1Check
    Corollary1Check
    Corollary2Check
CFG

    echo
    echo "============================================================"
    echo "EndpointBound = $B"
    echo "MaxSegments   = $MAX_SEGMENTS  (total bag cardinality)"
    echo "Input segments = $segment_count"
    echo "Sequences used to generate bags = $sequence_count"
    echo "Expected distinct bag multisegments = $distinct_bag_count"
    echo "============================================================"

    java -XX:+UseParallelGC \
        -cp "$TLA2TOOLS_JAR" \
        tlc2.TLC \
        -config "$cfg" \
        BoundedBagTests 2>&1 | tee "$log"

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
