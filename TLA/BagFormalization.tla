---- MODULE BagFormalization ----
EXTENDS Integers, FiniteSets, Sequences, Utils, Bags

\* --------------------
\* Segments - record representation
\* --------------------

Segment(a, b) ==
    [a |-> a, b |-> b]

Seg ==
    {s \in [a : Int, b : Int] :
        s.a <= s.b}

b(s) ==
    s.a

e(s) ==
    s.b

EmptySeg == \* questionable
    [a |-> 0, b |-> -1]

SegShiftLeft(s) ==
    Segment(b(s) - 1, e(s) - 1)

SegTruncateLeft(s) ==
    IF b(s) = e(s)
    THEN EmptySeg
    ELSE Segment(b(s) + 1, e(s))

Precedes(s1, s2) ==
    /\ b(s1) < b(s2)
    /\ e(s1) < e(s2)

SegSubsetEq(s1, s2) ==
    /\ b(s2) <= b(s1)
    /\ e(s1) <= e(s2)

Before(s1, s2) ==               \* used for a standard order of the multisegment
    \/ b(s1) < b(s2)
    \/ /\ b(s1) = b(s2)
       /\ e(s1) > e(s2)


\* --------------------
\* Multisegments
\* --------------------

Multisegments ==
    \* all functions from finite sets of segments to natural numbers > 0
    UNION {
        [S -> (Nat \ {0})] :
            S \in {T \in SUBSET Seg : IsFiniteSet(T)}
    }


SubMultisegment(N, M) ==
    N \sqsubseteq M


SameMultisegment(M, N) ==
    M = N


\* checks if there is a sequence of all the distinct elements of the multiset
\* where Precedes(sequence[i], sequence[i+1]) holds for all relevant i
IsLadder(M) ==
    /\ M # EmptyBag
    /\ BagCardinality(M) = Cardinality(BagToSet(M))
    /\ \E sequence \in Permutations(BagToSet(M)) :
        \A i \in 1..(BagCardinality(M) - 1) :
            Precedes(sequence[i], sequence[i + 1])

(* this only gives an order of the distinct elements
   and the order will be unique *)
StandardOrder(M) ==
    CHOOSE ordering \in
        {sequence \in
            [1..Cardinality(BagToSet(M)) -> BagToSet(M)] :
            /\ {sequence[i] : i \in DOMAIN sequence}
                    = BagToSet(M)
            /\ \A i \in
                1..(Cardinality(BagToSet(M)) - 1) :
                    Before(sequence[i], sequence[i + 1])
        } :
        TRUE


\* --------------------
\* Depth
\* --------------------

(* given a global index i, find the corresponding segment *)
segmentOf(M, i) ==
    LET
        PrefixOccurrences(j) ==
            {<<k, r>> :
                k \in 1..j,
                r \in 1..M[StandardOrder(M)[k]]
            }
    IN
        CHOOSE s \in BagToSet(M) :
            \E j \in 1..Cardinality(BagToSet(M)) :
                /\ StandardOrder(M)[j] = s
                /\ Cardinality(PrefixOccurrences(j - 1)) < i
                /\ i <= Cardinality(PrefixOccurrences(j))


(* given a global index i, find its distinct index
   in the standard ordering *)
FindIndex(M, i) ==
    CHOOSE j \in 1..Cardinality(BagToSet(M)) :
        segmentOf(M, i) = StandardOrder(M)[j]


(* depth of the segment at global index i *)
d(M, i) ==
    LET
        startIndex ==
            FindIndex(M, i)

        depthCandidates ==
            {j \in 0..(Cardinality(BagToSet(M)) - 1) :
                \E sequence \in
                    [1..(j + 1) ->
                        1..Cardinality(BagToSet(M))] :
                    /\ sequence[1] = startIndex
                    /\ \A k \in 1..j :
                        Precedes(
                            StandardOrder(M)[sequence[k]],
                            StandardOrder(M)[sequence[k + 1]]
                        )
            }
    IN
        CHOOSE depth \in depthCandidates :
            \A k \in depthCandidates :
                k <= depth


(* returns set of all global indices with given depth *)
depthBagCardinality(M, depth) ==
    {j \in 1..BagCardinality(M) :
        d(M, j) = depth}


(* the result is forced to be in increasing global-index order
   so the ordering becomes unique *)
AdmissibleEnumeration(M, depth) ==
    CHOOSE enumeration \in {
        sequence \in
            Permutations(depthBagCardinality(M, depth)) :

            /\ \A i \in
                1..(Cardinality(
                    depthBagCardinality(M, depth)) - 1) :
                    SegSubsetEq(
                        segmentOf(M, sequence[i + 1]),
                        segmentOf(M, sequence[i])
                    )

            /\ \A j \in
                1..(Cardinality(
                    depthBagCardinality(M, depth)) - 1) :
                    sequence[j] < sequence[j + 1]
    } :
        TRUE


IVee(M, i) ==
    LET
        depth ==
            d(M, i)

        enumeration ==
            AdmissibleEnumeration(M, depth)

        index ==
            CHOOSE j \in DOMAIN enumeration :
                enumeration[j] = i
    IN
        IF index = Len(enumeration)
        THEN enumeration[1]
        ELSE enumeration[index + 1]


SegmentTransform(M, i) ==
    Segment(
        b(segmentOf(M, i)),
        e(segmentOf(M, IVee(M, i)))
    )


DistinuishedIndicies(M) ==
    {i \in 1..BagCardinality(M) :
        i =
            AdmissibleEnumeration(M, d(M, i))[
                Cardinality(
                    depthBagCardinality(M, d(M, i))
                )
            ]
    }


RemainingBagCardinality(M) ==
    (1..BagCardinality(M)) \ DistinuishedIndicies(M)


l(M) ==
    LET
        transformedSegments ==
            {SegmentTransform(M, i) :
                i \in DistinuishedIndicies(M)}
    IN
        [s \in transformedSegments |->
            Cardinality(
                {i \in DistinuishedIndicies(M) :
                    SegmentTransform(M, i) = s}
            )
        ]


DerivedMultisegment(M) ==
    LET
        transformedSegments ==
            {SegmentTransform(M, i) :
                i \in RemainingBagCardinality(M)}
    IN
        [s \in transformedSegments |->
            Cardinality(
                {i \in RemainingBagCardinality(M) :
                    SegmentTransform(M, i) = s}
            )
        ]


K(M) ==
    <<l(M), DerivedMultisegment(M)>>


\* --------------------
\* The single MW step
\* --------------------

min(M) ==
    Min(
        {b(StandardOrder(M)[i]) :
            i \in 1..Len(StandardOrder(M))}
    )


\* 3.1a-3.1c
LeadingSequence(M) ==
    IF M = EmptyBag
    THEN <<>>
    ELSE
        LET
            FirstCandidate(i) ==
                /\ b(segmentOf(M, i)) = min(M)
                /\ \A globalIndex \in 1..BagCardinality(M) :
                    b(segmentOf(M, globalIndex)) = min(M)
                    =>
                    e(segmentOf(M, i))
                        <= e(segmentOf(M, globalIndex))

            FirstIndex ==
                CHOOSE i \in 1..BagCardinality(M) :
                    FirstCandidate(i)

            NextCandidate(i, q) ==
                /\ Precedes(
                    segmentOf(M, i),
                    segmentOf(M, q)
                )
                /\ b(segmentOf(M, q))
                    = b(segmentOf(M, i)) + 1

            NextIndex(i) ==
                CHOOSE next \in 1..BagCardinality(M) :
                    /\ NextCandidate(i, next)
                    /\ \A q \in 1..BagCardinality(M) :
                        NextCandidate(i, q)
                        =>
                        e(segmentOf(M, next))
                            <= e(segmentOf(M, q))

            Build[i \in 1..BagCardinality(M)] ==
                LET
                    successors ==
                        {q \in 1..BagCardinality(M) :
                            NextCandidate(i, q)}
                IN
                    IF successors = {}
                    THEN <<i>>
                    ELSE <<i>> \o Build[NextIndex(i)]

        IN
            Build[FirstIndex]


DeltaCircle(M) ==
    LET
        k ==
            Len(LeadingSequence(M))

        FirstSegment ==
            segmentOf(M, LeadingSequence(M)[1])
    IN
        Segment(
            b(FirstSegment),
            e(FirstSegment) + k - 1
        )


IStar(M) ==
    Range(LeadingSequence(M))


DeltaStar(M, i) ==
    IF i \in IStar(M)
    THEN SegTruncateLeft(segmentOf(M, i))
    ELSE segmentOf(M, i)


MCross(M) ==
    LET
        transformedSegments ==
            {DeltaStar(M, i) :
                i \in 1..BagCardinality(M)}
            \ {EmptySeg}
    IN
        [s \in transformedSegments |->
            Cardinality(
                {i \in 1..BagCardinality(M) :
                    DeltaStar(M, i) = s}
            )
        ]


MW(M) ==
    <<MCross(M), DeltaCircle(M)>>


\* --------------------
\* Lemma 1
\* --------------------

THEOREM Lemma1 ==
    \A M \in (Multisegments \ {EmptyBag}) :
        min(M) < min(l(M))
        =>
        /\ DerivedMultisegment(M) # EmptyBag
        /\ MCross(M) # EmptyBag

PROOF OMITTED


\* --------------------
\* The Statement - Corollary 3.4
\* --------------------

THEOREM Corollary1 ==
    \A M \in (Multisegments \ {EmptyBag}) :
        min(M) < min(l(M))
        =>
        K(MW(M)[1]) \o <<MW(M)[2]>>
        =
        <<K(M)[1]>> \o MW(K(M)[2])


\* --------------------
\* The Statement - Corollary 3.4
\* Alternative formulation
\* --------------------

THEOREM Corollary2 ==
    \A M \in (Multisegments \ {EmptyBag}) :
        min(M) < min(l(M))
        =>
        /\ l(M) = l(MCross(M))
        /\ DeltaCircle(M)
            = DeltaCircle(DerivedMultisegment(M))
        /\ DerivedMultisegment(MCross(M))
            = MCross(DerivedMultisegment(M))

=============