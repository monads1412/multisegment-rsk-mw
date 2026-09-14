---- MODULE RandomSequenceTests ----
EXTENDS FormalizedCorollary

\* ============================================================
\* Comprehensive randomized tests for FormalizedCorollary.tla
\*
\* The Python generator replaces the placeholders below and writes
\* RandomSequenceTests.tla.  Every sampled mathematical multisegment
\* is represented by one randomized sequence of its occurrences.
\*
\* AllDefinitionChecks is the same comprehensive structural suite as
\* the bounded harness, followed by Lemma 1 and all three formulations
\* of Corollary 3.4.
\* ============================================================

SampleCount == __SAMPLE_COUNT__
EndpointBound == __ENDPOINT_BOUND__
MaxDistinctSegments == __MAX_DISTINCT_SEGMENTS__
MaxMultiplicity == __MAX_MULTIPLICITY__
MaxTotalCardinality == __MAX_TOTAL_CARDINALITY__
RandomSeed == __RANDOM_SEED__

RandomMultisegments ==
{
__SEQUENCE_SAMPLES__
}

VARIABLE TestM

vars == <<TestM>>

Init ==
    TestM \in RandomMultisegments

Next ==
    UNCHANGED vars

Spec ==
    Init /\ [][Next]_vars

CorollaryHypothesis(M) ==
    min(M) < min(l(M))

InitCorollaryCases ==
    /\ TestM \in RandomMultisegments
    /\ CorollaryHypothesis(TestM)

SpecCorollaryCases ==
    InitCorollaryCases /\ [][Next]_vars

SampleCountCheck ==
    Cardinality(RandomMultisegments) = SampleCount

\* ============================================================
\* Independent reference helpers used by the tests
\* ============================================================

ValuesForTest(sequenceValue) ==
    {sequenceValue[indexValue] :
        indexValue \in 1..Len(sequenceValue)}

MultiplicityForTest(sequenceValue, elementValue) ==
    Cardinality(
        {indexValue \in 1..Len(sequenceValue) :
            sequenceValue[indexValue] = elementValue}
    )

SameMultisegmentForTest(leftValue, rightValue) ==
    /\ Len(leftValue) = Len(rightValue)
    /\ \A segmentValue \in
            (ValuesForTest(leftValue) \cup ValuesForTest(rightValue)) :
        MultiplicityForTest(leftValue, segmentValue)
            = MultiplicityForTest(rightValue, segmentValue)

SubMultisegmentForTest(leftValue, rightValue) ==
    \A segmentValue \in ValuesForTest(leftValue) :
        MultiplicityForTest(leftValue, segmentValue)
            <= MultiplicityForTest(rightValue, segmentValue)

ReverseForTest(sequenceValue) ==
    [indexValue \in 1..Len(sequenceValue) |->
        sequenceValue[Len(sequenceValue) - indexValue + 1]]

IsPermutationSequenceForTest(permutationValue, setValue) ==
    /\ DOMAIN permutationValue = 1..Cardinality(setValue)
    /\ ValuesForTest(permutationValue) = setValue
    /\ \A leftIndex \in DOMAIN permutationValue :
        \A rightIndex \in DOMAIN permutationValue :
            leftIndex # rightIndex
            =>
            permutationValue[leftIndex] # permutationValue[rightIndex]

IsLadderForTest(M) ==
    /\ M # <<>>
    /\ \E ordering \in
            [1..Len(M) -> IndexSet(M)] :
        /\ IsPermutationSequenceForTest(ordering, IndexSet(M))
        /\ \A position \in 1..(Len(M) - 1) :
            Precedes(
                M[ordering[position]],
                M[ordering[position + 1]]
            )

\* ============================================================
\* 1. Input-universe sanity
\* ============================================================

InputUniverseCheck ==
    /\ TestM \in RandomMultisegments
    /\ Len(TestM) \in 1..MaxTotalCardinality
    /\ Cardinality(ValuesForTest(TestM)) \in 1..MaxDistinctSegments
    /\ \A indexValue \in IndexSet(TestM) :
        LET segmentValue == TestM[indexValue]
        IN
            /\ segmentValue \in Seg
            /\ b(segmentValue) \in (-EndpointBound)..EndpointBound
            /\ e(segmentValue) \in (-EndpointBound)..EndpointBound
    /\ \A segmentValue \in ValuesForTest(TestM) :
        MultiplicityForTest(TestM, segmentValue) \in 1..MaxMultiplicity
    /\ IndexSet(TestM) = 1..Len(TestM)
    /\ Delta(TestM) = TestM

MultisegmentRelationCheck ==
    LET reversed == ReverseForTest(TestM)
    IN
        /\ SameMultisegment(TestM, reversed)
            = SameMultisegmentForTest(TestM, reversed)
        /\ SameMultisegment(TestM, TestM)
        /\ SubMultisegment(TestM, TestM)
            = SubMultisegmentForTest(TestM, TestM)

\* ============================================================
\* 2. Segment primitives
\* ============================================================

SegmentPrimitiveCheck ==
    \A indexValue \in IndexSet(TestM) :
        LET segmentValue == Delta(TestM)[indexValue]
        IN
            /\ segmentValue = Segment(b(segmentValue), e(segmentValue))
            /\ b(segmentValue) <= e(segmentValue)
            /\ SegShiftLeft(segmentValue)
                = Segment(b(segmentValue) - 1, e(segmentValue) - 1)
            /\ IF b(segmentValue) = e(segmentValue)
               THEN SegTruncateLeft(segmentValue) = EmptySeg
               ELSE
                   /\ SegTruncateLeft(segmentValue)
                        = Segment(b(segmentValue) + 1, e(segmentValue))
                   /\ SegTruncateLeft(segmentValue) \in Seg

\* ============================================================
\* 3. Depth: independently verify the chosen maximum
\* ============================================================

IsDepthChainForTest(M, startIndex, chainLength, chain) ==
    /\ chain[1] = startIndex
    /\ \A position \in 1..chainLength :
        Precedes(
            Delta(M)[chain[position]],
            Delta(M)[chain[position + 1]]
        )

DepthCheck ==
    /\ DOMAIN Depth(TestM) = IndexSet(TestM)
    /\ \A indexValue \in IndexSet(TestM) :
        LET depthValue == Depth(TestM)[indexValue]
        IN
            /\ depthValue \in 0..(Len(TestM) - 1)
            /\ \E chain \in
                    [1..(depthValue + 1) -> IndexSet(TestM)] :
                    IsDepthChainForTest(
                        TestM,
                        indexValue,
                        depthValue,
                        chain
                    )
            /\ IF depthValue = Len(TestM) - 1
               THEN TRUE
               ELSE
                   ~\E longerChain \in
                        [1..(depthValue + 2) -> IndexSet(TestM)] :
                        IsDepthChainForTest(
                            TestM,
                            indexValue,
                            depthValue + 1,
                            longerChain
                        )
    /\ d(TestM) \in Range(Depth(TestM))
    /\ \A indexValue \in IndexSet(TestM) :
        Depth(TestM)[indexValue] <= d(TestM)

\* ============================================================
\* 4. Depth fibers
\* ============================================================

DepthFiberCheck ==
    /\ \A depthValue \in Range(Depth(TestM)) :
        DepthFiber(TestM, depthValue)
            = {indexValue \in IndexSet(TestM) :
                Depth(TestM)[indexValue] = depthValue}
    /\ UNION {
            DepthFiber(TestM, depthValue) :
                depthValue \in Range(Depth(TestM))
       }
       = IndexSet(TestM)
    /\ \A depth1 \in Range(Depth(TestM)) :
        \A depth2 \in Range(Depth(TestM)) :
            depth1 # depth2
            =>
            DepthFiber(TestM, depth1)
                \cap DepthFiber(TestM, depth2)
                = {}

\* ============================================================
\* 5. Admissible enumerations
\*
\* This is important for CHOOSE: it checks that the value actually
\* returned by CHOOSE belongs to the fiber permutation set and
\* satisfies the admissibility predicate.
\* ============================================================

AdmissibleEnumerationCheck ==
    \A depthValue \in Range(Depth(TestM)) :
        LET
            fiberValue == DepthFiber(TestM, depthValue)
            enumeration ==
                AdmissibleEnumeration(TestM, depthValue)
        IN
            /\ fiberValue # {}
            /\ enumeration \in Enumerations(fiberValue)
            /\ IsPermutationSequenceForTest(enumeration, fiberValue)
            /\ Range(enumeration) = fiberValue
            /\ \A position \in 1..(Len(enumeration) - 1) :
                SegSubsetEq(
                    Delta(TestM)[enumeration[position + 1]],
                    Delta(TestM)[enumeration[position]]
                )

\* ============================================================
\* 6. j_k, I', and I''
\* ============================================================

IndexPartitionCheck ==
    /\ \A depthValue \in Range(Depth(TestM)) :
        LET enumeration ==
                AdmissibleEnumeration(TestM, depthValue)
        IN
            /\ jIndex(TestM, depthValue) = Last(enumeration)
            /\ jIndex(TestM, depthValue)
                \in DepthFiber(TestM, depthValue)
            /\ Depth(TestM)[jIndex(TestM, depthValue)]
                = depthValue
    /\ DistinguishedIndices(TestM) \subseteq IndexSet(TestM)
    /\ RemainingIndices(TestM) \subseteq IndexSet(TestM)
    /\ DistinguishedIndices(TestM)
        \cap RemainingIndices(TestM)
        = {}
    /\ DistinguishedIndices(TestM)
        \cup RemainingIndices(TestM)
        = IndexSet(TestM)
    /\ Cardinality(DistinguishedIndices(TestM))
        = Cardinality(Range(Depth(TestM)))

\* ============================================================
\* 7. i |-> i^vee
\* ============================================================

IVeeCheck ==
    LET vee == IVee(TestM)
    IN
        /\ DOMAIN vee = IndexSet(TestM)
        /\ Range(vee) = IndexSet(TestM)
        /\ IsInjective(vee)
        /\ \A leftIndex \in IndexSet(TestM) :
            \A rightIndex \in IndexSet(TestM) :
                leftIndex # rightIndex
                => vee[leftIndex] # vee[rightIndex]
        /\ \A indexValue \in IndexSet(TestM) :
            Depth(TestM)[vee[indexValue]]
                = Depth(TestM)[indexValue]
        /\ \A depthValue \in Range(Depth(TestM)) :
            LET enumeration ==
                    AdmissibleEnumeration(TestM, depthValue)
            IN
                \A position \in 1..Len(enumeration) :
                    vee[enumeration[position]]
                    = IF position = Len(enumeration)
                      THEN enumeration[1]
                      ELSE enumeration[position + 1]

\* ============================================================
\* 8. Delta'_i, l(m), and m'
\* ============================================================

SegmentTransformCheck ==
    \A indexValue \in IndexSet(TestM) :
        LET transformed == SegmentTransform(TestM, indexValue)
        IN
            /\ transformed \in Seg
            /\ b(transformed) = b(Delta(TestM)[indexValue])
            /\ e(transformed)
                = e(Delta(TestM)[IVee(TestM)[indexValue]])
            /\ bTransform(TestM, indexValue) = b(transformed)
            /\ eTransform(TestM, indexValue) = e(transformed)

LadderConstructionCheck ==
    LET ladderValue == l(TestM)
    IN
        /\ Len(ladderValue) = d(TestM) + 1
        /\ \A position \in 1..Len(ladderValue) :
            /\ ladderValue[position]
                = SegmentTransform(
                    TestM,
                    jIndex(TestM, position - 1)
                  )
            /\ ladderValue[position] \in Seg
        /\ IsLadder(ladderValue)
        /\ IsLadderForTest(ladderValue)

DerivedMultisegmentCheck ==
    LET
        remaining == RemainingIndices(TestM)
        derived == DerivedMultisegment(TestM)
        transformedValues ==
            {SegmentTransform(TestM, indexValue) :
                indexValue \in remaining}
    IN
        /\ Len(derived) = Cardinality(remaining)
        /\ Range(derived) = transformedValues
        /\ \A position \in IndexSet(derived) :
            derived[position] \in Seg
        /\ \A segmentValue \in transformedValues :
            Multiplicity(derived, segmentValue)
            = Cardinality(
                {indexValue \in remaining :
                    SegmentTransform(TestM, indexValue)
                        = segmentValue}
              )

KConstructionCheck ==
    /\ K(TestM)[1] = l(TestM)
    /\ K(TestM)[2] = DerivedMultisegment(TestM)

\* ============================================================
\* 9. min(m)
\* ============================================================

MinimumCheck ==
    /\ \E indexValue \in IndexSet(TestM) :
        b(Delta(TestM)[indexValue]) = min(TestM)
    /\ \A indexValue \in IndexSet(TestM) :
        min(TestM) <= b(Delta(TestM)[indexValue])

\* ============================================================
\* 10. Leading sequence: independently check 3.1a--3.1c
\* ============================================================

LeadingCandidateSequencesForTest(M) ==
    UNION {
        [1..sequenceLength -> IndexSet(M)] :
            sequenceLength \in 1..Len(M)
    }

LeadingFirstOKForTest(M, indexValue) ==
    /\ b(Delta(M)[indexValue]) = min(M)
    /\ \A candidate \in IndexSet(M) :
        b(Delta(M)[candidate]) = min(M)
        =>
        e(Delta(M)[indexValue]) <= e(Delta(M)[candidate])

LeadingNextCandidateForTest(M, indexValue, nextIndex) ==
    /\ Precedes(Delta(M)[indexValue], Delta(M)[nextIndex])
    /\ b(Delta(M)[nextIndex]) = b(Delta(M)[indexValue]) + 1

LeadingNextOKForTest(M, indexValue, nextIndex) ==
    /\ LeadingNextCandidateForTest(M, indexValue, nextIndex)
    /\ \A candidate \in IndexSet(M) :
        LeadingNextCandidateForTest(M, indexValue, candidate)
        =>
        e(Delta(M)[nextIndex]) <= e(Delta(M)[candidate])

LeadingSequenceCheck ==
    LET leading == LeadingSequence(TestM)
    IN
        /\ leading \in LeadingCandidateSequencesForTest(TestM)
        /\ LeadingFirstOKForTest(TestM, leading[1])
        /\ \A position \in 1..(Len(leading) - 1) :
            LeadingNextOKForTest(
                TestM,
                leading[position],
                leading[position + 1]
            )
        /\ ~\E candidate \in IndexSet(TestM) :
            LeadingNextCandidateForTest(
                TestM,
                Last(leading),
                candidate
            )
        /\ Cardinality(ValuesForTest(leading)) = Len(leading)
        /\ IStar(TestM) = Range(leading)

\* ============================================================
\* 11. Delta_i*, m^cross, Delta^circle, and MW
\* ============================================================

MWConstructionCheck ==
    LET
        leading == LeadingSequence(TestM)
        kept ==
            {indexValue \in IndexSet(TestM) :
                DeltaStar(TestM, indexValue) # EmptySeg}
        crossed == MCross(TestM)
        crossedValues ==
            {DeltaStar(TestM, indexValue) :
                indexValue \in kept}
        circle == DeltaCircle(TestM)
    IN
        /\ \A indexValue \in IndexSet(TestM) :
            /\ DeltaStar(TestM, indexValue)
                = IF indexValue \in IStar(TestM)
                  THEN SegTruncateLeft(Delta(TestM)[indexValue])
                  ELSE Delta(TestM)[indexValue]
            /\ \/ DeltaStar(TestM, indexValue) = EmptySeg
               \/ DeltaStar(TestM, indexValue) \in Seg
        /\ Len(crossed) = Cardinality(kept)
        /\ Range(crossed) = crossedValues
        /\ EmptySeg \notin Range(crossed)
        /\ \A segmentValue \in crossedValues :
            Multiplicity(crossed, segmentValue)
            = Cardinality(
                {indexValue \in kept :
                    DeltaStar(TestM, indexValue) = segmentValue}
              )
        /\ circle \in Seg
        /\ b(circle) = min(TestM)
        /\ e(circle) = min(TestM) + Len(leading) - 1
        /\ MW(TestM)[1] = crossed
        /\ MW(TestM)[2] = circle

\* ============================================================
\* 12. All structural/object checks in one conjunction
\* ============================================================

AllDefinitionChecks ==
    /\ MultisegmentRelationCheck
    /\ SegmentPrimitiveCheck
    /\ DepthCheck
    /\ DepthFiberCheck
    /\ AdmissibleEnumerationCheck
    /\ IndexPartitionCheck
    /\ IVeeCheck
    /\ SegmentTransformCheck
    /\ LadderConstructionCheck
    /\ DerivedMultisegmentCheck
    /\ KConstructionCheck
    /\ MinimumCheck
    /\ LeadingSequenceCheck
    /\ MWConstructionCheck

\* IMPORTANT: the random-test config uses RandomUniverseCheck.  Folding
\* AllDefinitionChecks into it makes one invariant cover the full
\* object-level validation suite.
RandomUniverseCheck ==
    /\ InputUniverseCheck
    /\ AllDefinitionChecks

\* ============================================================
\* 13. Previous Lemma 1 check
\* ============================================================

Lemma1Check ==
    IF CorollaryHypothesis(TestM)
    THEN
        /\ DerivedMultisegment(TestM) # <<>>
        /\ MCross(TestM) # <<>>
    ELSE TRUE

\* ============================================================
\* 14. Previous Corollary 3.4 checks -- all three formulations
\*
\* The explicit nonempty checks make failures from Lemma 1 visible
\* before we call operators such as min on derived/crossed objects.
\* ============================================================

Corollary1Check ==
    IF ~CorollaryHypothesis(TestM)
    THEN TRUE
    ELSE
        LET
            derived == DerivedMultisegment(TestM)
            crossed == MCross(TestM)
        IN
            /\ derived # <<>>
            /\ crossed # <<>>
            /\ l(TestM) = l(crossed)
            /\ DeltaCircle(TestM) = DeltaCircle(derived)
            /\ SameMultisegment(
                   DerivedMultisegment(crossed),
                   MCross(derived)
               )
            /\ SameMultisegmentForTest(
                   DerivedMultisegment(crossed),
                   MCross(derived)
               )

KxIdForTest(pairValue) ==
    LET kValue == K(pairValue[1])
    IN <<kValue[1], kValue[2], pairValue[2]>>

IdxMWForTest(pairValue) ==
    LET mwValue == MW(pairValue[2])
    IN <<pairValue[1], mwValue[1], mwValue[2]>>

SameResultForTest(leftValue, rightValue) ==
    /\ leftValue[1] = rightValue[1]
    /\ SameMultisegment(leftValue[2], rightValue[2])
    /\ SameMultisegmentForTest(leftValue[2], rightValue[2])
    /\ leftValue[3] = rightValue[3]

Corollary2Check ==
    IF ~CorollaryHypothesis(TestM)
    THEN TRUE
    ELSE
        LET
            derived == DerivedMultisegment(TestM)
            crossed == MCross(TestM)
        IN
            /\ derived # <<>>
            /\ crossed # <<>>
            /\ SameResultForTest(
                   KxIdForTest(MW(TestM)),
                   IdxMWForTest(K(TestM))
               )

Corollary3Check ==
    IF ~CorollaryHypothesis(TestM)
    THEN TRUE
    ELSE
        LET
            derived == DerivedMultisegment(TestM)
            crossed == MCross(TestM)
        IN
            /\ derived # <<>>
            /\ crossed # <<>>
            /\ K(TestM)[1] = K(crossed)[1]
            /\ MW(TestM)[2] = MW(derived)[2]
            /\ SameMultisegment(
                   K(crossed)[2],
                   MW(derived)[1]
               )
            /\ SameMultisegmentForTest(
                   K(crossed)[2],
                   MW(derived)[1]
               )

=============================================================================
