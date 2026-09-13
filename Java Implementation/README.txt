COMPREHENSIVE RANDOMIZED TESTER FOR Segment + MultiSegment

FILES
-----
ComprehensiveRandomTester.java
run_java_random_tests.sh

WHAT IT TESTS
-------------
The tester uses an independent brute-force/reference implementation and compares
your Java code against it.

Segment:
- isSegment
- segmentToSet
- precedes
- subsetEq
- compareTo ordering and antisymmetry

MultiSegment representation:
- size
- distinct sorted segment list
- cumulative frequencies
- global-index -> distinct-index mapping
- segmentAt
- firstOccurrenceIndex

Depth/K-side machinery:
- longest chain starting at every global index
- depth of every global index
- every depth fiber
- admissible enumerations
- SegmentTransform
- distinguished indices
- l(m)
- verifies l(m) is actually a ladder
- DerivedMultisegment

MW-side machinery:
- LeadingIndices against an independent Definition 3.1 construction
- independent validity check of 3.1a, 3.1b, and 3.1c
- DeltaStar for every index
- DeltaCircle
- MCross

Lemma / Corollary:
For every sampled m satisfying min(m) < min(l(m)):
- DerivedMultisegment(m) is nonempty
- MCross(m) is nonempty
- l(m) = l(MCross(m))
- DeltaCircle(m) = DeltaCircle(DerivedMultisegment(m))
- DerivedMultisegment(MCross(m)) =
  MCross(DerivedMultisegment(m))

It also reports exactly how many sampled multisegments satisfied the
non-vacuous lemma/corollary hypothesis.

The tester additionally checks repeated calls for stability, so lazy caches
must not change mathematical results.

RUNNING
-------
Put the two tester files either:
1. beside Segment.java and MultiSegment.java, or
2. in the root of a Maven-style project whose sources are:
   src/main/java/com/salma/Segment.java
   src/main/java/com/salma/MultiSegment.java

Then:

  bash run_java_random_tests.sh 1000 10 4 2 5 12345

Arguments, in order:

  1000   number of distinct random mathematical multisegments
  10     segment endpoints range from -10 through 10
  4      at most 4 distinct segment values in one multisegment
  2      multiplicity of a chosen segment is between 1 and 2
  5      total multisegment cardinality is at most 5
  12345  reproducible random seed

A serious larger run:

  bash run_java_random_tests.sh 10000 20 4 2 5 12345

Use several seeds for independent batches, e.g. 12345, 54321, 98765.

GUAVA
-----
The script tries to find Guava beside the script, in ./lib, in /usr/share/java,
or in your local Maven repository (~/.m2).

If that fails:

  export GUAVA_JAR=/full/path/to/guava-<version>.jar

then rerun.

IMPORTANT CURRENT CODE ISSUE
----------------------------
Your pasted Segment.subsetEq currently says:

  s1.b <= s2.b && s2.e <= s1.e

That means "s2 is contained in s1".

Your TLA+ SegSubsetEq(s1,s2), and the mathematical meaning used by the tester,
is "s1 is contained in s2":

  s2.b <= s1.b && s1.e <= s2.e

So the comprehensive tester is expected to fail immediately on subsetEq until
that method is corrected. This method appears not to be used by MultiSegment,
so fixing it should not change the rest of the implementation.
