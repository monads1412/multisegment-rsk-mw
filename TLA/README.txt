COMPREHENSIVE RANDOMIZED TLA+ TEST HARNESS
==========================================

Purpose
-------
This package complements the exhaustive bounded tests.
It samples a fixed number of DISTINCT mathematical multisegments from a much
larger universe, then runs the full structural/object checks plus the lemma and
corollary checks.

The SAME mathematical random sample can be tested in:
  1. FormalizedCorollary.tla   (sequence representation)
  2. BagFormalization.tla      (bag representation)

Required files beside this package
----------------------------------
  Utils.tla
  FormalizedCorollary.tla      (for sequence or both mode)
  BagFormalization.tla         (for bag or both mode)
  tla2tools.jar

Run
---
  bash run_random_tests.sh \
      SAMPLE_COUNT ENDPOINT_BOUND MAX_DISTINCT_SEGMENTS \
      MAX_MULTIPLICITY MAX_TOTAL_CARDINALITY SEED MODE

MODE is one of:
  sequence
  bag
  both

Example: comprehensive sequence stress test
-------------------------------------------
  bash run_random_tests.sh 2000 20 4 2 5 12345 sequence

Meaning:
  - exactly 2000 distinct mathematical multisegments
  - every segment endpoint lies in -20..20
  - 1..4 distinct segment values per multisegment
  - multiplicity of each chosen segment is 1..2
  - total number of segment occurrences is at most 5
  - seed 12345 makes the sample reproducible

Example: test the SAME 500 mathematical multisegments in both implementations
-----------------------------------------------------------------------------
  bash run_random_tests.sh 500 20 4 2 5 12345 both

Why MAX_TOTAL_CARDINALITY exists
--------------------------------
The expensive operators grow much faster with the number of segment
occurrences than with endpoint range.  A wide endpoint range is cheap;
a large multisegment can make Depth / admissible-enumeration / leading-sequence
checks combinatorial.  This cap lets you widen endpoints and multiplicities
without accidentally creating enormous individual TLC evaluations.

What is checked: FormalizedCorollary
------------------------------------
The sequence test includes the comprehensive bounded-test suite:
  - input representation, same/sub-multisegment helpers
  - segment primitives
  - Depth and maximal-chain witness/nonexistence of a longer chain
  - depth fibers
  - admissible enumerations
  - j_k and distinguished/remaining-index partition
  - i |-> i^vee permutation and cycle behavior
  - SegmentTransform and endpoint identities
  - l(m), including ladder validity
  - DerivedMultisegment with exact multiplicities
  - K packaging
  - min(m)
  - LeadingSequence and 3.1a / 3.1b / 3.1c
  - I*, DeltaStar, MCross with exact multiplicities
  - DeltaCircle
  - MW packaging
  - Lemma 1
  - Corollary 3.4 formulations 1, 2, and 3
  - an independent multiplicity-based multisegment equality check

What is checked: BagFormalization
---------------------------------
The bag test independently checks:
  - bag/input constraints and segment primitives
  - StandardOrder
  - segmentOf multiplicity/global-index coverage
  - FindIndex
  - depth, including maximal-chain witness/nonexistence of a longer chain
  - depthGlobalIndices partition
  - AdmissibleEnumeration
  - IVee cycle behavior and fiber preservation
  - SegmentTransform
  - distinguished/remaining-index partition
  - l(m), exact bag multiplicities, and ladder validity
  - DerivedMultisegment exact bag multiplicities
  - K packaging
  - min(m)
  - LeadingSequence and 3.1a / 3.1b / 3.1c
  - I*, DeltaStar, MCross exact bag multiplicities
  - DeltaCircle
  - MW packaging
  - Lemma 1
  - both bag Corollary 3.4 formulations

Counting non-vacuous corollary cases
------------------------------------
The theorem is an implication.  Inputs where

    min(M) < min(l(M))

does not hold pass the corollary vacuously.

To run an extra diagnostic pass whose initial states are exactly the sampled
inputs satisfying the hypothesis, use:

  COUNT_COROLLARY_CASES=1 bash run_random_tests.sh 2000 20 4 2 5 12345 sequence

The line

  Finished computing initial states: N distinct states generated

in the diagnostic pass gives the number of sampled representations for which
the corollary hypothesis is true.  This extra pass costs additional time.

Suggested sample sizes
----------------------
For the sequence implementation with MAX_TOTAL_CARDINALITY <= 5:
  - 2000 is a strong first stress test.
  - 5000 is a good next target if runtime is comfortable.
  - several seeds are preferable to putting everything into one seed.

For the bag implementation, individual cases are much more expensive:
  - start around 250-500 per seed.
  - move to 1000 if runtime is acceptable.

A useful campaign is, for example, five sequence runs of 2000 cases each with
five different seeds.  That gives 10,000 sampled multisegments while retaining
reproducibility and making any failing batch easy to isolate.

Generated files
---------------
The generator writes:
  RandomSequenceTests.tla
  RandomBagTests.tla

These are deliberately kept after a run so a failure can be reproduced and
inspected with the same seed and sample.

Random testing is evidence, not a proof
---------------------------------------
A PASS means every sampled input satisfied every enabled structural and theorem
check.  It does not prove the unbounded theorem.  The exhaustive bounded tests
and the randomized tests are complementary: exhaustive gives total coverage of
a small universe; randomized gives sparse coverage of a much wider universe.
