#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   bash run_java_random_tests.sh \
#       SAMPLES ENDPOINT_BOUND MAX_DISTINCT MAX_MULTIPLICITY MAX_TOTAL_CARDINALITY SEED
#
# Example:
#   bash run_java_random_tests.sh 10000 20 4 2 5 12345
#
# Put this script and ComprehensiveRandomTester.java either:
#   (A) beside Segment.java and MultiSegment.java, or
#   (B) in the root of a Maven-style project containing
#       src/main/java/com/salma/Segment.java
#       src/main/java/com/salma/MultiSegment.java
#
# The script tries to locate guava automatically. If it cannot, set:
#   export GUAVA_JAR=/full/path/to/guava-<version>.jar

if [[ $# -ne 6 ]]; then
    echo "Usage:"
    echo "  bash run_java_random_tests.sh SAMPLES ENDPOINT_BOUND MAX_DISTINCT MAX_MULTIPLICITY MAX_TOTAL_CARDINALITY SEED"
    echo
    echo "Example:"
    echo "  bash run_java_random_tests.sh 10000 20 4 2 5 12345"
    exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

TESTER="$SCRIPT_DIR/ComprehensiveRandomTester.java"

if [[ ! -f "$TESTER" ]]; then
    echo "Could not find ComprehensiveRandomTester.java beside this script."
    exit 2
fi

if [[ -f "$SCRIPT_DIR/Segment.java" && -f "$SCRIPT_DIR/MultiSegment.java" ]]; then
    SOURCE_DIR="$SCRIPT_DIR"
elif [[ -f "$SCRIPT_DIR/src/main/java/com/salma/Segment.java" && -f "$SCRIPT_DIR/src/main/java/com/salma/MultiSegment.java" ]]; then
    SOURCE_DIR="$SCRIPT_DIR/src/main/java/com/salma"
else
    echo "Could not find Segment.java and MultiSegment.java."
    echo "Put this package beside those files, or run it from your project root."
    exit 2
fi

find_guava() {
    if [[ -n "${GUAVA_JAR:-}" && -f "${GUAVA_JAR}" ]]; then
        printf '%s\n' "$GUAVA_JAR"
        return 0
    fi

    local candidate=""

    for candidate in \
        "$SCRIPT_DIR"/guava*.jar \
        "$SCRIPT_DIR"/lib/guava*.jar \
        /usr/share/java/guava.jar \
        /usr/share/java/guava-*.jar
    do
        if [[ -f "$candidate" ]]; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done

    candidate="$(
        find "$HOME/.m2/repository/com/google/guava/guava" \
            -type f -name 'guava-*.jar' 2>/dev/null \
            | sort -V \
            | tail -n 1
    )"

    if [[ -n "$candidate" && -f "$candidate" ]]; then
        printf '%s\n' "$candidate"
        return 0
    fi

    return 1
}

if ! GUAVA_PATH="$(find_guava)"; then
    echo "Could not locate the Guava jar."
    echo
    echo "If Guava is already installed, set its path, for example:"
    echo "  export GUAVA_JAR=/path/to/guava-33.4.8-jre.jar"
    echo
    echo "Then rerun this command."
    exit 2
fi

BUILD_DIR="$SCRIPT_DIR/.java-random-test-build"
rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR"

echo
echo "Using Guava:"
echo "  $GUAVA_PATH"
echo
echo "Compiling Segment.java, MultiSegment.java, and tester..."

javac \
    -cp "$GUAVA_PATH" \
    -d "$BUILD_DIR" \
    "$SOURCE_DIR/Segment.java" \
    "$SOURCE_DIR/MultiSegment.java" \
    "$TESTER"

echo "Compilation successful."
echo

java \
    -ea \
    -cp "$BUILD_DIR:$GUAVA_PATH" \
    com.salma.ComprehensiveRandomTester \
    "$@"
