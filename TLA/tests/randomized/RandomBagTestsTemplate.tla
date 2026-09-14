---- MODULE RandomBagTests ----
EXTENDS BagFormalization

\* ============================================================
\* Comprehensive randomized tests for BagFormalization.tla
\*
\* The Python generator replaces the placeholders below and writes
\* RandomBagTests.tla.  The same mathematical multisegments used by
\* RandomSequenceTests are converted here to bags.
\* ============================================================

SampleCount == __SAMPLE_COUNT__
EndpointBound == __ENDPOINT_BOUND__
MaxDistinctSegments == __MAX_DISTINCT_SEGMENTS__
MaxMultiplicity == __MAX_MULTIPLICITY__
MaxTotalCardinality == __MAX_TOTAL_CARDINALITY__
RandomSeed == __RANDOM_SEED__

\* A descriptor is a sequence of <<segment, multiplicity>> pairs.
SampleDescriptors ==
{
__BAG_DESCRIPTORS__
}

DescriptorToBag(descriptor) ==
    LET
        support ==
            {descriptor[position][1] : position \in DOMAIN descriptor}

        MultiplicityOf(segmentValue) ==
            LET position ==
                    CHOOSE p \in DOMAIN descriptor :
                        descriptor[p][1] = segmentValue
            IN descriptor[position][2]
    IN
        [segmentValue \in support |-> MultiplicityOf(segmentValue)]

RandomMultisegments ==
    {DescriptorToBag(descriptor) : descriptor \in SampleDescriptors}

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
\* Independent helpers
\* ============================================================

DepthValues(M) ==
    {d(M, globalIndex) :
        globalIndex \in 1..BagCardinality(M)}

SameBagForTest(leftValue, rightValue) ==
    /\ BagToSet(leftValue) = BagToSet(rightValue)
    /\ \A segmentValue \in BagToSet(leftValue) :
        leftValue[segmentValue] = rightValue[segmentValue]

IsEnumerationForTest(enumeration, setValue) ==
    /\ DOMAIN enumeration = 1..Cardinality(setValue)
    /\ Range(enumeration) = setValue
    /\ IsInjective(enumeration)

IsLadderForTest(M) ==
    /\ M # EmptyBag
    /\ BagCardinality(M) = Cardinality(BagToSet(M))
    /\ \E ordering \in Enumerations(BagToSet(M)) :
        \A position \in 1..(Len(ordering) - 1) :
            Precedes(
                ordering[position],
                ordering[position + 1]
            )

\* ============================================================
\* 1. Input universe and segment primitives
\* ============================================================

InputUniverseCheck ==
    /\ IsABag(TestM)
    /\ TestM \in RandomMultisegments
    /\ Cardinality(BagToSet(TestM)) \in 1..MaxDistinctSegments
    /\ BagCardinality(TestM) \in 1..MaxTotalCardinality
    /\ \A segmentValue \in BagToSet(TestM) :
        /\ segmentValue \in Seg
        /\ b(segmentValue) \in (-EndpointBound)..EndpointBound
        /\ e(segmentValue) \in (-EndpointBound)..EndpointBound
        /\ TestM[segmentValue] \in 1..MaxMultiplicity
    /\ SameMultisegment(TestM, TestM)
    /\ SameBagForTest(TestM, TestM)
    /\ SubMultisegment(TestM, TestM)

SegmentPrimitiveCheck ==
    \A segmentValue \in BagToSet(TestM) :
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
\* 2. Standard order and global-index reconstruction
\* ============================================================

StandardOrderCheck ==
    LET ordering == StandardOrder(TestM)
    IN
        /\ ordering \in Enumerations(BagToSet(TestM))
        /\ IsEnumerationForTest(ordering, BagToSet(TestM))
        /\ \A position \in 1..(Len(ordering) - 1) :
            Before(ordering[position], ordering[position + 1])

GlobalIndexCoverageCheck ==
    /\ \A globalIndex \in 1..BagCardinality(TestM) :
        segmentOf(TestM, globalIndex) \in BagToSet(TestM)
    /\ \A segmentValue \in BagToSet(TestM) :
        Cardinality(
            {globalIndex \in 1..BagCardinality(TestM) :
                segmentOf(TestM, globalIndex) = segmentValue}
        )
        = TestM[segmentValue]

FindIndexCheck ==
    \A globalIndex \in 1..BagCardinality(TestM) :
        LET distinctIndex == FindIndex(TestM, globalIndex)
        IN
            /\ distinctIndex \in 1..Cardinality(BagToSet(TestM))
            /\ StandardOrder(TestM)[distinctIndex]
                = segmentOf(TestM, globalIndex)

\* ============================================================
\* 3. Depth and depth fibers
\* ============================================================

IsDepthChainForTest(M, startDistinctIndex, chainLength, chain) ==
    /\ chain[1] = startDistinctIndex
    /\ \A position \in 1..chainLength :
        Precedes(
            StandardOrder(M)[chain[position]],
            StandardOrder(M)[chain[position + 1]]
        )

DepthCheck ==
    \A globalIndex \in 1..BagCardinality(TestM) :
        LET
            depthValue == d(TestM, globalIndex)
            startDistinctIndex == FindIndex(TestM, globalIndex)
            supportSize == Cardinality(BagToSet(TestM))
        IN
            /\ depthValue \in 0..(supportSize - 1)
            /\ \E chain \in [1..(depthValue + 1) -> 1..supportSize] :
                IsDepthChainForTest(
                    TestM,
                    startDistinctIndex,
                    depthValue,
                    chain
                )
            /\ IF depthValue = supportSize - 1
               THEN TRUE
               ELSE
                   ~\E longerChain \in
                        [1..(depthValue + 2) -> 1..supportSize] :
                        IsDepthChainForTest(
                            TestM,
                            startDistinctIndex,
                            depthValue + 1,
                            longerChain
                        )

DepthFiberCheck ==
    /\ \A depthValue \in DepthValues(TestM) :
        depthGlobalIndices(TestM, depthValue)
            = {globalIndex \in 1..BagCardinality(TestM) :
                d(TestM, globalIndex) = depthValue}
    /\ UNION {
            depthGlobalIndices(TestM, depthValue) :
                depthValue \in DepthValues(TestM)
       }
       = 1..BagCardinality(TestM)
    /\ \A depth1 \in DepthValues(TestM) :
        \A depth2 \in DepthValues(TestM) :
            depth1 # depth2
            =>
            depthGlobalIndices(TestM, depth1)
                \cap depthGlobalIndices(TestM, depth2)
                = {}

\* ============================================================
\* 4. Admissible enumerations and i^vee
\* ============================================================

AdmissibleEnumerationCheck ==
    \A depthValue \in DepthValues(TestM) :
        LET
            fiber == depthGlobalIndices(TestM, depthValue)
            enumeration == AdmissibleEnumeration(TestM, depthValue)
        IN
            /\ fiber # {}
            /\ enumeration \in Enumerations(fiber)
            /\ IsEnumerationForTest(enumeration, fiber)
            /\ \A position \in 1..(Len(enumeration) - 1) :
                /\ SegSubsetEq(
                    segmentOf(TestM, enumeration[position + 1]),
                    segmentOf(TestM, enumeration[position])
                   )
                /\ enumeration[position] < enumeration[position + 1]

IVeeCheck ==
    /\ \A globalIndex \in 1..BagCardinality(TestM) :
        IVee(TestM, globalIndex)
            \in depthGlobalIndices(TestM, d(TestM, globalIndex))
    /\ \A depthValue \in DepthValues(TestM) :
        LET enumeration == AdmissibleEnumeration(TestM, depthValue)
        IN
            /\ {IVee(TestM, globalIndex) :
                    globalIndex \in depthGlobalIndices(TestM, depthValue)}
                = depthGlobalIndices(TestM, depthValue)
            /\ \A position \in 1..Len(enumeration) :
                IVee(TestM, enumeration[position])
                = IF position = Len(enumeration)
                  THEN enumeration[1]
                  ELSE enumeration[position + 1]

\* ============================================================
\* 5. Segment transforms, distinguished indices, l(m), and m'
\* ============================================================

SegmentTransformCheck ==
    \A globalIndex \in 1..BagCardinality(TestM) :
        LET transformed == SegmentTransform(TestM, globalIndex)
        IN
            /\ transformed \in Seg
            /\ b(transformed) = b(segmentOf(TestM, globalIndex))
            /\ e(transformed)
                = e(segmentOf(TestM, IVee(TestM, globalIndex)))

IndexPartitionCheck ==
    /\ DistinuishedIndicies(TestM) \subseteq 1..BagCardinality(TestM)
    /\ RemainingBagCardinality(TestM) \subseteq 1..BagCardinality(TestM)
    /\ DistinuishedIndicies(TestM)
        \cap RemainingBagCardinality(TestM)
        = {}
    /\ DistinuishedIndicies(TestM)
        \cup RemainingBagCardinality(TestM)
        = 1..BagCardinality(TestM)
    /\ Cardinality(DistinuishedIndicies(TestM))
        = Cardinality(DepthValues(TestM))
    /\ \A depthValue \in DepthValues(TestM) :
        Last(AdmissibleEnumeration(TestM, depthValue))
            \in DistinuishedIndicies(TestM)

LadderConstructionCheck ==
    LET
        ladderValue == l(TestM)
        transformedValues ==
            {SegmentTransform(TestM, globalIndex) :
                globalIndex \in DistinuishedIndicies(TestM)}
    IN
        /\ IsABag(ladderValue)
        /\ BagCardinality(ladderValue)
            = Cardinality(DistinuishedIndicies(TestM))
        /\ BagToSet(ladderValue) = transformedValues
        /\ \A segmentValue \in transformedValues :
            ladderValue[segmentValue]
            = Cardinality(
                {globalIndex \in DistinuishedIndicies(TestM) :
                    SegmentTransform(TestM, globalIndex) = segmentValue}
              )
        /\ IsLadder(ladderValue)
        /\ IsLadderForTest(ladderValue)

DerivedMultisegmentCheck ==
    LET
        remaining == RemainingBagCardinality(TestM)
        derived == DerivedMultisegment(TestM)
        transformedValues ==
            {SegmentTransform(TestM, globalIndex) :
                globalIndex \in remaining}
    IN
        /\ IsABag(derived)
        /\ BagCardinality(derived) = Cardinality(remaining)
        /\ BagToSet(derived) = transformedValues
        /\ \A segmentValue \in transformedValues :
            derived[segmentValue]
            = Cardinality(
                {globalIndex \in remaining :
                    SegmentTransform(TestM, globalIndex) = segmentValue}
              )

KConstructionCheck ==
    /\ K(TestM)[1] = l(TestM)
    /\ K(TestM)[2] = DerivedMultisegment(TestM)

\* ============================================================
\* 6. min(m) and the leading sequence
\* ============================================================

MinimumCheck ==
    /\ \E globalIndex \in 1..BagCardinality(TestM) :
        b(segmentOf(TestM, globalIndex)) = min(TestM)
    /\ \A globalIndex \in 1..BagCardinality(TestM) :
        min(TestM) <= b(segmentOf(TestM, globalIndex))

LeadingFirstOKForTest(M, globalIndex) ==
    /\ b(segmentOf(M, globalIndex)) = min(M)
    /\ \A candidate \in 1..BagCardinality(M) :
        b(segmentOf(M, candidate)) = min(M)
        =>
        e(segmentOf(M, globalIndex)) <= e(segmentOf(M, candidate))

LeadingNextCandidateForTest(M, globalIndex, nextIndex) ==
    /\ Precedes(
        segmentOf(M, globalIndex),
        segmentOf(M, nextIndex)
       )
    /\ b(segmentOf(M, nextIndex))
        = b(segmentOf(M, globalIndex)) + 1

LeadingNextOKForTest(M, globalIndex, nextIndex) ==
    /\ LeadingNextCandidateForTest(M, globalIndex, nextIndex)
    /\ \A candidate \in 1..BagCardinality(M) :
        LeadingNextCandidateForTest(M, globalIndex, candidate)
        =>
        e(segmentOf(M, nextIndex)) <= e(segmentOf(M, candidate))

LeadingSequenceCheck ==
    LET leading == LeadingSequence(TestM)
    IN
        /\ leading # <<>>
        /\ DOMAIN leading = 1..Len(leading)
        /\ Len(leading) \in 1..BagCardinality(TestM)
        /\ \A position \in DOMAIN leading :
            leading[position] \in 1..BagCardinality(TestM)
        /\ LeadingFirstOKForTest(TestM, leading[1])
        /\ \A position \in 1..(Len(leading) - 1) :
            LeadingNextOKForTest(
                TestM,
                leading[position],
                leading[position + 1]
            )
        /\ ~\E candidate \in 1..BagCardinality(TestM) :
            LeadingNextCandidateForTest(
                TestM,
                Last(leading),
                candidate
            )
        /\ Cardinality(Range(leading)) = Len(leading)
        /\ IStar(TestM) = Range(leading)

\* ============================================================
\* 7. Delta_i*, m^cross, Delta^circle, and MW
\* ============================================================

MWConstructionCheck ==
    LET
        leading == LeadingSequence(TestM)
        crossed == MCross(TestM)
        survivingValues ==
            {DeltaStar(TestM, globalIndex) :
                globalIndex \in 1..BagCardinality(TestM)}
            \ {EmptySeg}
        survivingIndices ==
            {globalIndex \in 1..BagCardinality(TestM) :
                DeltaStar(TestM, globalIndex) # EmptySeg}
        circle == DeltaCircle(TestM)
    IN
        /\ \A globalIndex \in 1..BagCardinality(TestM) :
            /\ DeltaStar(TestM, globalIndex)
                = IF globalIndex \in IStar(TestM)
                  THEN SegTruncateLeft(segmentOf(TestM, globalIndex))
                  ELSE segmentOf(TestM, globalIndex)
            /\ \/ DeltaStar(TestM, globalIndex) = EmptySeg
               \/ DeltaStar(TestM, globalIndex) \in Seg
        /\ IsABag(crossed)
        /\ BagCardinality(crossed) = Cardinality(survivingIndices)
        /\ BagToSet(crossed) = survivingValues
        /\ \A segmentValue \in survivingValues :
            crossed[segmentValue]
            = Cardinality(
                {globalIndex \in survivingIndices :
                    DeltaStar(TestM, globalIndex) = segmentValue}
              )
        /\ circle \in Seg
        /\ b(circle) = min(TestM)
        /\ e(circle) = min(TestM) + Len(leading) - 1
        /\ MW(TestM)[1] = crossed
        /\ MW(TestM)[2] = circle

\* ============================================================
\* 8. All object-level checks
\* ============================================================

AllDefinitionChecks ==
    /\ SegmentPrimitiveCheck
    /\ StandardOrderCheck
    /\ GlobalIndexCoverageCheck
    /\ FindIndexCheck
    /\ DepthCheck
    /\ DepthFiberCheck
    /\ AdmissibleEnumerationCheck
    /\ IVeeCheck
    /\ SegmentTransformCheck
    /\ IndexPartitionCheck
    /\ LadderConstructionCheck
    /\ DerivedMultisegmentCheck
    /\ KConstructionCheck
    /\ MinimumCheck
    /\ LeadingSequenceCheck
    /\ MWConstructionCheck

RandomUniverseCheck ==
    /\ InputUniverseCheck
    /\ AllDefinitionChecks

\* ============================================================
\* 9. Lemma 1 and both Corollary 3.4 formulations
\* ============================================================

Lemma1Check ==
    IF CorollaryHypothesis(TestM)
    THEN
        /\ DerivedMultisegment(TestM) # EmptyBag
        /\ MCross(TestM) # EmptyBag
    ELSE TRUE

Corollary1Check ==
    IF ~CorollaryHypothesis(TestM)
    THEN TRUE
    ELSE
        LET
            derived == DerivedMultisegment(TestM)
            crossed == MCross(TestM)
        IN
            /\ derived # EmptyBag
            /\ crossed # EmptyBag
            /\ K(MW(TestM)[1]) \o <<MW(TestM)[2]>>
                = <<K(TestM)[1]>> \o MW(K(TestM)[2])

Corollary2Check ==
    IF ~CorollaryHypothesis(TestM)
    THEN TRUE
    ELSE
        LET
            derived == DerivedMultisegment(TestM)
            crossed == MCross(TestM)
        IN
            /\ derived # EmptyBag
            /\ crossed # EmptyBag
            /\ l(TestM) = l(crossed)
            /\ DeltaCircle(TestM) = DeltaCircle(derived)
            /\ DerivedMultisegment(crossed) = MCross(derived)
            /\ SameBagForTest(
                   DerivedMultisegment(crossed),
                   MCross(derived)
               )

=============================================================================
