---- MODULE BoundedBagTests ----
EXTENDS BagFormalization

\* ============================================================
\* Finite input universe for the bag implementation
\* ============================================================

CONSTANTS EndpointBound, MaxSegments

EndpointValues ==
    (-EndpointBound)..EndpointBound

\* First construct every endpoint pair, then keep only valid segments.
\* Using different local names avoids collisions with b(s) and e(s).
AllBoundedSegmentRecords ==
    {Segment(endpointPair[1], endpointPair[2]) :
        endpointPair \in (EndpointValues \X EndpointValues)}

BoundedSegments ==
    {segmentValue \in AllBoundedSegmentRecords :
        b(segmentValue) <= e(segmentValue)}

\* Convert a nonempty sequence to the bag represented by that sequence.
\* Different orderings of the same sequence elements therefore collapse
\* to the same bag, while repetitions become multiplicities.
SequenceToBag(sequence) ==
    LET
        support ==
            {sequence[indexValue] : indexValue \in DOMAIN sequence}
    IN
        [segmentValue \in support |->
            Cardinality(
                {indexValue \in DOMAIN sequence :
                    sequence[indexValue] = segmentValue}
            )
        ]

\* Generate every nonempty sequence of 1..MaxSegments bounded segments.
\* Mapping them through SequenceToBag yields every bag whose total
\* cardinality is between 1 and MaxSegments.
BoundedInputSequences ==
    UNION {
        [1..numSegments -> BoundedSegments] :
            numSegments \in 1..MaxSegments
    }

BoundedMultisegments ==
    {SequenceToBag(sequence) :
        sequence \in BoundedInputSequences}


\* ============================================================
\* One TLC initial state for each distinct bounded bag
\* ============================================================

VARIABLE TestM

vars == <<TestM>>

Init ==
    TestM \in BoundedMultisegments

Next ==
    UNCHANGED vars

Spec ==
    Init /\ [][Next]_vars


\* ============================================================
\* Basic bounded-universe sanity check
\* ============================================================

BoundedUniverseCheck ==
    /\ IsABag(TestM)
    /\ BagCardinality(TestM) \in 1..MaxSegments
    /\ \A segmentValue \in BagToSet(TestM) :
        segmentValue \in BoundedSegments


\* ============================================================
\* Bag-specific machinery checks
\* ============================================================

\* StandardOrder must really enumerate all distinct segments exactly once
\* and must satisfy the ordering relation used by the implementation.
StandardOrderCheck ==
    LET
        ordering == StandardOrder(TestM)
    IN
        /\ ordering \in Enumerations(BagToSet(TestM))
        /\ \A position \in 1..(Len(ordering) - 1) :
            Before(ordering[position], ordering[position + 1])


\* segmentOf should expand the bag into exactly BagCardinality(M) global
\* occurrences, with each segment appearing exactly its multiplicity times.
GlobalIndexCoverageCheck ==
    /\ \A globalIndex \in 1..BagCardinality(TestM) :
        segmentOf(TestM, globalIndex) \in BagToSet(TestM)
    /\ \A segmentValue \in BagToSet(TestM) :
        Cardinality(
            {globalIndex \in 1..BagCardinality(TestM) :
                segmentOf(TestM, globalIndex) = segmentValue}
        )
        = TestM[segmentValue]


DepthValues(M) ==
    {d(M, globalIndex) :
        globalIndex \in 1..BagCardinality(M)}


\* Before relying on CHOOSE, check that an admissible enumeration actually
\* exists for every depth that occurs.  If it exists, also verify that the
\* value selected by AdmissibleEnumeration satisfies the defining conditions.
AdmissibleEnumerationCheck ==
    \A depthValue \in DepthValues(TestM) :
        LET
            fiber == depthGlobalIndices(TestM, depthValue)

            IsAdmissible(enumeration) ==
                /\ enumeration \in Enumerations(fiber)
                /\ \A position \in 1..(Cardinality(fiber) - 1) :
                    SegSubsetEq(
                        segmentOf(TestM, enumeration[position + 1]),
                        segmentOf(TestM, enumeration[position])
                    )
                /\ \A position \in 1..(Cardinality(fiber) - 1) :
                    enumeration[position] < enumeration[position + 1]

            ExistsAdmissible ==
                \E enumeration \in Enumerations(fiber) :
                    IsAdmissible(enumeration)
        IN
            IF ~ExistsAdmissible
            THEN FALSE
            ELSE IsAdmissible(
                AdmissibleEnumeration(TestM, depthValue)
            )


\* ============================================================
\* Bounded version of Lemma 1
\* ============================================================

Lemma1Check ==
    IF min(TestM) < min(l(TestM))
    THEN
        /\ DerivedMultisegment(TestM) # EmptyBag
        /\ MCross(TestM) # EmptyBag
    ELSE TRUE


\* ============================================================
\* Bounded versions of the two Corollary 3.4 formulations
\* ============================================================
\*
\* Under the theorem hypothesis, Lemma 1 says that both m' and m^cross
\* are nonempty.  We guard this explicitly so that a Lemma 1 failure is
\* reported as FALSE rather than causing a later undefined evaluation.

Corollary1Check ==
    IF ~(min(TestM) < min(l(TestM)))
    THEN TRUE
    ELSE
        LET
            derivedValue == DerivedMultisegment(TestM)
            crossedValue == MCross(TestM)
        IN
            IF derivedValue = EmptyBag \/ crossedValue = EmptyBag
            THEN FALSE
            ELSE
                K(MW(TestM)[1]) \o <<MW(TestM)[2]>>
                =
                <<K(TestM)[1]>> \o MW(K(TestM)[2])


Corollary2Check ==
    IF ~(min(TestM) < min(l(TestM)))
    THEN TRUE
    ELSE
        LET
            derivedValue == DerivedMultisegment(TestM)
            crossedValue == MCross(TestM)
        IN
            IF derivedValue = EmptyBag \/ crossedValue = EmptyBag
            THEN FALSE
            ELSE
                /\ l(TestM) = l(crossedValue)
                /\ DeltaCircle(TestM) = DeltaCircle(derivedValue)
                /\ DerivedMultisegment(crossedValue)
                    = MCross(derivedValue)

=============================================================================
