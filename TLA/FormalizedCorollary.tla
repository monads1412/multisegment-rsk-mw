---- MODULE FormalizedCorollary ----
EXTENDS Integers, FiniteSets, Sequences, Utils

\* --------------------
\* Segments
\* --------------------

Segment(a, b) ==
    <<a, b>>

Seg ==
    {s \in Int \X Int : s[1] <= s[2]}

EmptySeg == <<>> \* the empty segment is not part of Seg

b(s) ==
    s[1]

e(s) ==
    s[2]

SegShiftLeft(s) ==
    Segment(b(s) - 1, e(s) - 1)

SegTruncateLeft(s) ==
    IF b(s) = e(s)
    THEN EmptySeg
    ELSE Segment(b(s) + 1, e(s))

Precedes(s1, s2) ==
    \* returns s1 ≺ s2
    /\ b(s1) < b(s2)
    /\ e(s1) < e(s2)

SegSubsetEq(s1, s2) ==
    \* checks if s1 is a subset of s2
    /\ b(s2) <= b(s1)
    /\ e(s1) <= e(s2)

\* --------------------
\* Multisegments
\* --------------------

Multisegments ==
    Seq(Seg)


SubMultisegment(N, M) ==
    SubMultiset(N, M)


SameMultisegment(M, N) ==
    SameBag(M, N)


IndexSet(M) ==
    1..Len(M)

Delta(M) == M                                               \* sticking to paper notation (redundant)

IsLadder(M) ==
    /\ M # <<>>                                              \* a ladder is nonempty
    /\ \E R \in Enumerations(IndexSet(M)) :
        \A i \in 1..(Len(M) - 1) :
            Precedes(M[R[i]], M[R[i + 1]])                   \* Delta_{R[i]} ≺ Delta_{R[i+1]}                                


\* --------------------
\* Depth
\* --------------------

Depth(M) ==
    LET
        IsDepthChain(i, j, Chain) ==
            /\ Chain[1] = i                                  \* the chain starts at index i
            /\ \A r \in 1..j :
                Precedes(
                    Delta(M)[Chain[r]],
                    Delta(M)[Chain[r + 1]]
                )                                            \* each segment precedes the next one
    IN
        [i \in IndexSet(M) |->
            Max({
                j \in 0..(Len(M) - 1) :
                    \E Chain \in [1..(j + 1) -> IndexSet(M)] :
                        IsDepthChain(i, j, Chain)             \* there exists a chain of length j from i
            })
        ]

d(M) ==
    \* returns the depth of the multisegment M
    IF M = <<>>
    THEN 0
    ELSE Max(Range(Depth(M)))

\* --------------------
\* The Map K
\* --------------------

DepthFiber(M, k) ==
    Fiber(Depth(M), k)                                       \* d_M^{-1}(k)


AdmissibleEnumeration(M, k) ==
    LET
        F == DepthFiber(M, k)                                \* depth fiber at k

        IsAdmissible(P) ==
            \A r \in 1..(Cardinality(F) - 1) :
                SegSubsetEq(
                    Delta(M)[P[r + 1]],
                    Delta(M)[P[r]]
                )                                            \* P satisfies the admissibility condition
    IN
        CHOOSE P \in Enumerations(F) :
            IsAdmissible(P)                                  \* choose any admissible enumeration                                             


jIndex(M, k) ==
    IF k \in Range(Depth(M))
    THEN Last(AdmissibleEnumeration(M, k))
    ELSE 0


IVee(M) ==
    LET
        Cycles ==
            {AdmissibleEnumeration(M, k) :
                k \in Range(Depth(M))}                          \* one cycle for each depth fiber
    IN
        PermutationFromCycles(IndexSet(M), Cycles)               \* permutation i |-> i^vee induced by these cycles


\* 2.1a 
SegmentTransform(M, i) ==
    \* this is ∆′_i
    Segment(
        b(Delta(M)[i]),
        e(Delta(M)[IVee(M)[i]])
    )

\* 2.1b
DistinguishedIndices(M) ==
    {jIndex(M, k) : k \in Range(Depth(M))}

RemainingIndices(M) ==
    \* this is I''=I\I'
    IndexSet(M) \ DistinguishedIndices(M)

\* 2.1c
l(M) ==
    [r \in 1..(d(M) + 1) |->
        SegmentTransform(M, jIndex(M, r - 1))
    ]


DerivedMultisegment(M) ==
    EnumerateValues(
        [i \in RemainingIndices(M) |->
            SegmentTransform(M, i)]
    )                                                        \* m' = sum of Delta'_i for i in I''

    
\* 2.2
bTransform(M, i) ==
    b(SegmentTransform(M, i))

eTransform(M, i) ==
    e(SegmentTransform(M, i))

K(M) ==
    <<l(M), DerivedMultisegment(M)>>

\* --------------------
\* The single MW step
\* --------------------

min(M) ==
    Min({b(Delta(M)[i]) : i \in IndexSet(M)})  


\* 3.1a-3.1c
LeadingSequence(M) ==
    LET
        CandidateSequences ==
            UNION {
                [1..k -> IndexSet(M)] :
                k \in 1..Len(M)
            }                                                \* all possible nonempty index sequences of relevant length

        FirstOK(i) ==
            /\ b(Delta(M)[i]) = min(M)                       \* Delta_i begins at min M
            /\ \A q \in IndexSet(M) :
                b(Delta(M)[q]) = min(M)
                =>
                e(Delta(M)[i]) <= e(Delta(M)[q])             \* Delta_i has minimal ending among these segments

        NextCandidate(i, q) ==
            /\ Precedes(Delta(M)[i], Delta(M)[q])            \* Delta_i ≺ Delta_q
            /\ b(Delta(M)[q]) = b(Delta(M)[i]) + 1           \* Delta_q begins exactly one later

        NextOK(i, next) ==
            /\ NextCandidate(i, next)                         \* next is an eligible successor
            /\ \A q \in IndexSet(M) :
                NextCandidate(i, q)
                =>
                e(Delta(M)[next]) <= e(Delta(M)[q])          \* next has minimal ending among eligible successors

        IsValid(S) ==
            /\ FirstOK(S[1])                                 \* first index satisfies (3.1a)
            /\ \A r \in 1..(Len(S) - 1) :
                NextOK(S[r], S[r + 1])                       \* successive indices satisfy (3.1b)
            /\ ~\E q \in IndexSet(M) :
                NextCandidate(Last(S), q)                    \* no successor exists after the last index: (3.1c)

    IN
        CHOOSE S \in CandidateSequences :
            IsValid(S)                                      \* choose one complete leading sequence                             


IStar(M) ==
    \* I* = {i_1, ..., i_k}
    Range(LeadingSequence(M))                                     \* image of the chosen leading sequence


DeltaStar(M, i) ==
    IF i \in IStar(M)                                             \* if i is one of the leading indices
    THEN SegTruncateLeft(Delta(M)[i])                             \* Delta_i* = -Delta_i
    ELSE Delta(M)[i]                                              \* otherwise Delta_i* = Delta_i


\* 3.2
MCross(M) ==
    LET
        KeptIndices ==
            {i \in IndexSet(M) :
                DeltaStar(M, i) # EmptySeg}                  \* discard empty transformed segments
    IN
        EnumerateValues(
            [i \in KeptIndices |->
                DeltaStar(M, i)]
        )                                                    \* m^cross = sum of the nonempty Delta_i*


DeltaCircle(M) ==
    Segment(
        min(M),                                                \* left endpoint is min m
        min(M) + Len(LeadingSequence(M)) - 1                   \* right endpoint is min m + k - 1
    )


MW(M) ==
    <<MCross(M), DeltaCircle(M)>>                                \* MW(m) = (m^cross, Delta^circ(m))


\* --------------------
\* Lemma 1
\* --------------------

THEOREM Lemma1 ==
    \A m \in (Multisegments\{<<>>}) :
        min(m) < min(l(m))
        =>
        /\ DerivedMultisegment(m) # <<>>
        /\ MCross(m) # <<>>

PROOF OMITTED 


\* --------------------
\* The Statement - Corollary 3.4
\* First alternative formulation
\* --------------------

THEOREM Corollary1 ==
    \A M \in (Multisegments \ {<<>>}) :                     \* for every nonempty multisegment M
        min(M) < min(l(M))                                  \* assuming min M < min l(M)
        =>
        /\ l(M) = l(MCross(M))                              \* l(m) = l(m^cross)
        /\ DeltaCircle(M)
            = DeltaCircle(DerivedMultisegment(M))           \* Delta^circle(m) = Delta^circle(m')
        /\ SameMultisegment(
               DerivedMultisegment(MCross(M)),
               MCross(DerivedMultisegment(M))
           )                                                \* (m^cross)' = (m')^cross as multisegments

PROOF OMITTED


\* --------------------
\* The Statement - Corollary 3.4
\* Second alternative formulation
\* --------------------

THEOREM Corollary2 ==
    LET
        KxId(P) ==
            LET
                KP == K(P[1])                               \* apply K to the first component
            IN
                <<KP[1], KP[2], P[2]>>                     \* (K x Id)(P)

        IdxMW(P) ==
            LET
                MWP == MW(P[2])                             \* apply MW to the second component
            IN
                <<P[1], MWP[1], MWP[2]>>                   \* (Id x MW)(P)

        SameResult(P, Q) ==
            /\ P[1] = Q[1]                                 \* ladder components are equal
            /\ SameMultisegment(P[2], Q[2])                \* multisegment components are equal
            /\ P[3] = Q[3]                                 \* distinguished segments are equal

    IN
        \A M \in (Multisegments \ {<<>>}) :
            min(M) < min(l(M))
            =>
            SameResult(
                KxId(MW(M)),
                IdxMW(K(M))
            )                                               \* (K x Id)(MW(m)) = (Id x MW)(K(m))

PROOF OMITTED


\* --------------------
\* The Statement - Corollary 3.4
\* Third alternative formulation
\* --------------------

THEOREM Corollary3 ==
    \A M \in (Multisegments \ {<<>>}) :
        min(M) < min(l(M))
        =>
        /\ K(M)[1] = K(MW(M)[1])[1]                        \* l(m) = l(m^cross)
        /\ MW(M)[2] = MW(K(M)[2])[2]                       \* Delta^circ(m) = Delta^circ(m')
        /\ SameMultisegment(
               K(MW(M)[1])[2],
               MW(K(M)[2])[1]
           )                                                \* (m^cross)' = (m')^cross as multisegments

PROOF OMITTED



==============