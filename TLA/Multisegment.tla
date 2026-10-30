----------- MODULE Multisegment -------------

EXTENDS Integers, FiniteSets, Bags, Sequences

(**************************************************************************************)
(* We start with some utility functions.                                              *)
(**************************************************************************************)

Min(S) == CHOOSE n \in S : \A m \in S : n <= m
Max(S) == CHOOSE n \in S : \A m \in S : n >= m

\* Last element of a sequence:
Last(seq) == seq[Len(seq)]

\* Concatenate a sequence of sequences, preserving order and repetitions.
Concat(seqs) ==
    LET prefix[n \in 0..Len(seqs)] ==
        IF n = 0 THEN <<>> ELSE prefix[n - 1] \o seqs[n]
    IN prefix[Len(seqs)]

Fiber(f, y) == {x \in DOMAIN f : f[x] = y}

SeqToBag(s) ==
    [x \in {s[i] : i \in DOMAIN s} |-> Cardinality(Fiber(s, x))]

(**************************************************************************************)
(* Next we formalize the notions from the paper.                                      *)
(**************************************************************************************)

Segment == {D \in SUBSET Int : \E b, e \in Int : b <= e /\ D = b..e}
b(D) == Min(D)
e(D) == Max(D)

MinusSegment(D) == (b(D)+1)..e(D)
ShiftLeftSegment(D) == (b(D)-1)..(e(D)-1)

D1 \prec D2 ==  b(D1) < b(D2) /\ e(D1) < e(D2)

SegmentInclusion ==
    \A D1, D2 \in Segment :
        D2 \subseteq D1 <=> b(D1) <= b(D2) /\ e(D2) <= e(D1)

Multisegment ==
    UNION {[S -> (Nat \ {0})] :
        S \in {T \in SUBSET Segment : IsFiniteSet(T)}}

min(M) == Min({b(D) : D \in BagToSet(M)})

(**************************************************************************************)
(* N \sqsubseteq M (in Bags.tla) means N is a sub-multisegment of M: each segment     *)
(* has no greater multiplicity.                                                       *)
(**************************************************************************************)

Ladder ==
    {M \in Multisegment :
        /\ M # EmptyBag
        /\ \A D \in BagToSet(M) : M[D] = 1
        /\ \A D1, D2 \in BagToSet(M) :
            D1 # D2 => (D1 \prec D2 \/ D2 \prec D1)}

SegmentDepth(M, D) ==
    LET S == BagToSet(M)
    IN Max({j \in 0..(Cardinality(S) - 1) :
        \E chain \in [0..j -> S] :
            /\ chain[0] = D
            /\ \A r \in 0..(j - 1) : chain[r] \prec chain[r + 1]})

(**************************************************************************************)
(* NOTE: We don't care if SegmentDepth(M, D) is meaningless outside our intended      *)
(* domain (M a multisegment, D in M). That does not introduce unsoudness in our       *)
(* theory.                                                                            *)
(**************************************************************************************)

Depth(M) == Max({SegmentDepth(M, D) : D \in BagToSet(M)})

\* Page 1, Fact: segments of equal depth are equal or strictly nested.
EqualDepthContainment ==
    \A M \in Multisegment : \A D1, D2 \in BagToSet(M) :
        SegmentDepth(M, D1) = SegmentDepth(M, D2) =>
            (D1 \subseteq D2 \/ D2 \subseteq D1)

SegmentsAtDepth(M, k) ==
    {D \in BagToSet(M) : SegmentDepth(M, D) = k}

\* Fiber elements, repeated according to their multiplicity, ordered by containment.
AdmissibleEnumeration(M, k) ==
    LET depthKElems == SegmentsAtDepth(M, k)
        fiber == [D \in depthKElems |-> M[D]]
    IN CHOOSE s \in [1..BagCardinality(fiber) -> depthKElems] :
        /\ SeqToBag(s) = fiber
        /\ \A r \in 1..(Len(s) - 1) : s[r + 1] \subseteq s[r]

\* Rotate right endpoints within a depth fiber, keeping the left endpoints.
TransformedEnumeration(M, k) ==
    LET segments == AdmissibleEnumeration(M, k)
        last == Len(segments)
        Next(r) == IF r = last THEN 1 ELSE r + 1
    IN [r \in DOMAIN segments |-> b(segments[r])..e(segments[Next(r)])]

\* Equation (2.2): the selected segment has both maximal endpoints in its fiber.
HighestLadderEndpoints ==
    \A M \in Multisegment \ {EmptyBag} : \A k \in 0..Depth(M) :
        LET depthKElems == SegmentsAtDepth(M, k)
            selected == Last(TransformedEnumeration(M, k))
        IN /\ b(selected) = Max({b(D) : D \in depthKElems})
           /\ e(selected) = Max({e(D) : D \in depthKElems})

HighestLadder(M) ==
    SeqToBag([i \in 1..(Depth(M)+1) |->
        Last(TransformedEnumeration(M, i-1))])

DerivedMultisegment(M) ==
    SeqToBag(Concat([i \in 1..(Depth(M)+1) |->
      LET enumK == TransformedEnumeration(M, i-1)
      IN SubSeq(enumK, 1, Len(enumK)-1)]))

\* The single RSK step, for nonempty M.
K(M) == <<HighestLadder(M), DerivedMultisegment(M)>>

=============================================
