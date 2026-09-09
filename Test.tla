---- MODULE Test ----

EXTENDS FormalizedCorollary


\* ============================================================
\* FIXTURES
\* ============================================================

\*
\* DepthM:
\*
\*   1 -> [1,4]    depth 1
\*   2 -> [2,3]    depth 1
\*   3 -> [4,8]    depth 0
\*
\* At depth 1, the unique admissible enumeration is <<1,2>>
\* because [2,3] is contained in [1,4].
\*
\* At depth 0, the unique enumeration is <<3>>.
\*
\* This is deliberately only length 3 so Depth is cheap.
\*

DepthM ==
    <<Segment(1,4),
      Segment(2,3),
      Segment(4,8)>>

ExpectedL ==
    <<Segment(4,8),
      Segment(2,4)>>

ExpectedDerived ==
    <<Segment(1,3)>>


\*
\* LeadM has a unique leading sequence:
\*
\*   1 -> [1,1]
\*   2 -> [2,2]
\*   3 -> [3,4]
\*
\* so LeadingSequence(LeadM) = <<1,2,3>>
\*

LeadM ==
    <<Segment(1,1),
      Segment(2,2),
      Segment(3,4)>>


\*
\* Here only index 1 belongs to the leading sequence.
\* Useful for testing the "ELSE" branch of DeltaStar.
\*

ShortLeadM ==
    <<Segment(1,3),
      Segment(2,2)>>


\*
\* Fixtures for bag/multisegment tests.
\*

BagA == Segment(1,2)
BagB == Segment(3,4)

BagBig ==
    <<BagA, BagA, BagB>>

BagSmall ==
    <<BagA, BagB>>

BagReordered ==
    <<BagB, BagA, BagA>>


\* ============================================================
\* SEGMENT OPERATORS
\* ============================================================


\* ------------------------------------------------------------
\* Segment
\* ------------------------------------------------------------

TestSegment ==
    /\ Segment(2,5) = <<2,5>>
    /\ Segment(-1,3) = <<-1,3>>
    /\ Segment(4,4) = <<4,4>>


\* ------------------------------------------------------------
\* Seg
\* ------------------------------------------------------------

TestSeg ==
    /\ Segment(1,4) \in Seg
    /\ Segment(-3,-1) \in Seg
    /\ Segment(5,5) \in Seg
    /\ ~(Segment(5,2) \in Seg)


\* ------------------------------------------------------------
\* EmptySeg
\* ------------------------------------------------------------

TestEmptySeg ==
    /\ EmptySeg = <<>>
    /\ ~(EmptySeg \in Seg)


\* ------------------------------------------------------------
\* b
\* ------------------------------------------------------------

TestB ==
    /\ b(Segment(2,7)) = 2
    /\ b(Segment(-3,4)) = -3


\* ------------------------------------------------------------
\* e
\* ------------------------------------------------------------

TestE ==
    /\ e(Segment(2,7)) = 7
    /\ e(Segment(-3,4)) = 4


\* ------------------------------------------------------------
\* SegShiftLeft
\* ------------------------------------------------------------

TestSegShiftLeft ==
    /\ SegShiftLeft(Segment(3,7)) = Segment(2,6)
    /\ SegShiftLeft(Segment(0,0)) = Segment(-1,-1)


\* ------------------------------------------------------------
\* SegTruncateLeft
\* ------------------------------------------------------------

TestSegTruncateLeft ==
    /\ SegTruncateLeft(Segment(2,5)) = Segment(3,5)
    /\ SegTruncateLeft(Segment(4,4)) = EmptySeg


\* ------------------------------------------------------------
\* Precedes
\* ------------------------------------------------------------

TestPrecedes ==
    /\ Precedes(
           Segment(1,3),
           Segment(2,4)
       )

    \* beginning increases, but ending does not
    /\ ~Precedes(
           Segment(1,4),
           Segment(2,3)
       )

    \* ending increases, but beginning does not
    /\ ~Precedes(
           Segment(3,4),
           Segment(2,5)
       )


\* ------------------------------------------------------------
\* SegSubsetEq
\* ------------------------------------------------------------

TestSegSubsetEq ==
    /\ SegSubsetEq(
           Segment(2,3),
           Segment(1,4)
       )

    \* equality is allowed
    /\ SegSubsetEq(
           Segment(1,4),
           Segment(1,4)
       )

    /\ ~SegSubsetEq(
           Segment(1,5),
           Segment(1,4)
       )


\* ============================================================
\* MULTISEGMENT OPERATORS
\* ============================================================


\* ------------------------------------------------------------
\* Multisegments
\* ------------------------------------------------------------

TestMultisegments ==
    /\ DepthM \in Multisegments
    /\ <<>> \in Multisegments
    /\ ~(<<Segment(4,2)>> \in Multisegments)


\* ------------------------------------------------------------
\* SubMultisegment
\*
\* Also checks that multiplicity matters.
\* ------------------------------------------------------------

TestSubMultisegment ==
    /\ SubMultisegment(BagSmall, BagBig)
    /\ ~SubMultisegment(BagBig, BagSmall)


\* ------------------------------------------------------------
\* SameMultisegment
\*
\* Same elements and multiplicities, different ordering.
\* ------------------------------------------------------------

TestSameMultisegment ==
    /\ SameMultisegment(BagBig, BagReordered)
    /\ ~SameMultisegment(BagBig, BagSmall)


\* ------------------------------------------------------------
\* IndexSet
\* ------------------------------------------------------------

TestIndexSet ==
    /\ IndexSet(DepthM) = {1,2,3}
    /\ IndexSet(<<Segment(1,1)>>) = {1}


\* ------------------------------------------------------------
\* Delta
\*
\* Since a sequence is already a function on 1..Len(M),
\* Delta(M) is extensionally equal to M.
\* ------------------------------------------------------------

TestDelta ==
    /\ Delta(DepthM) = DepthM
    /\ Delta(DepthM)[1] = Segment(1,4)
    /\ Delta(DepthM)[3] = Segment(4,8)


\* ------------------------------------------------------------
\* IsLadder
\* ------------------------------------------------------------

LadderM ==
    <<Segment(5,8),
      Segment(2,4)>>

NonLadderM ==
    <<Segment(1,4),
      Segment(2,3)>>

TestIsLadder ==
    /\ IsLadder(LadderM)
    /\ ~IsLadder(NonLadderM)
    /\ ~IsLadder(<<>>)


\* ============================================================
\* DEPTH
\* ============================================================


\* ------------------------------------------------------------
\* Depth
\*
\* DepthM:
\*
\*   1 -> depth 1
\*   2 -> depth 1
\*   3 -> depth 0
\* ------------------------------------------------------------

TestDepth ==
    LET
        D == Depth(DepthM)
    IN
        /\ DOMAIN D = {1,2,3}
        /\ D[1] = 1
        /\ D[2] = 1
        /\ D[3] = 0


\* ------------------------------------------------------------
\* d
\* ------------------------------------------------------------

TestD ==
    /\ d(DepthM) = 1
    /\ d(<<>>) = 0


\* ============================================================
\* K-CONSTRUCTION
\* ============================================================


\* ------------------------------------------------------------
\* DepthFiber
\* ------------------------------------------------------------

TestDepthFiber ==
    /\ DepthFiber(DepthM,0) = {3}
    /\ DepthFiber(DepthM,1) = {1,2}
    /\ DepthFiber(DepthM,2) = {}


\* ------------------------------------------------------------
\* AdmissibleEnumeration
\*
\* Both are unique, so CHOOSE creates no test ambiguity.
\* ------------------------------------------------------------

TestAdmissibleEnumeration ==
    /\ AdmissibleEnumeration(DepthM,0) = <<3>>
    /\ AdmissibleEnumeration(DepthM,1) = <<1,2>>


\* ------------------------------------------------------------
\* jIndex
\* ------------------------------------------------------------

TestJIndex ==
    /\ jIndex(DepthM,0) = 3
    /\ jIndex(DepthM,1) = 2

    \* depth 2 does not occur
    /\ jIndex(DepthM,2) = 0


\* ------------------------------------------------------------
\* IVee
\*
\* cycles:
\*
\*   (1 2)
\*   (3)
\*
\* hence:
\*   1 |-> 2
\*   2 |-> 1
\*   3 |-> 3
\* ------------------------------------------------------------

TestIVee ==
    LET
        V == IVee(DepthM)
    IN
        /\ V[1] = 2
        /\ V[2] = 1
        /\ V[3] = 3
        /\ V \in [IndexSet(DepthM) -> IndexSet(DepthM)]


\* ------------------------------------------------------------
\* SegmentTransform
\*
\* Delta'_1 = [1,3]
\* Delta'_2 = [2,4]
\* Delta'_3 = [4,8]
\* ------------------------------------------------------------

TestSegmentTransform ==
    /\ SegmentTransform(DepthM,1) = Segment(1,3)
    /\ SegmentTransform(DepthM,2) = Segment(2,4)
    /\ SegmentTransform(DepthM,3) = Segment(4,8)


\* ------------------------------------------------------------
\* DistinguishedIndices
\*
\* j_0 = 3
\* j_1 = 2
\* ------------------------------------------------------------

TestDistinguishedIndices ==
    DistinguishedIndices(DepthM) = {2,3}


\* ------------------------------------------------------------
\* RemainingIndices
\* ------------------------------------------------------------

TestRemainingIndices ==
    RemainingIndices(DepthM) = {1}


\* ------------------------------------------------------------
\* l
\*
\* l(m) =
\*   <<Delta'_j0, Delta'_j1>>
\* = <<[4,8], [2,4]>>
\* ------------------------------------------------------------

TestL ==
    /\ l(DepthM) = ExpectedL
    /\ IsLadder(l(DepthM))


\* ------------------------------------------------------------
\* DerivedMultisegment
\*
\* Only index 1 remains, so there is no arbitrary ordering here.
\* ------------------------------------------------------------

TestDerivedMultisegment ==
    DerivedMultisegment(DepthM) = ExpectedDerived


\* ------------------------------------------------------------
\* bTransform
\* ------------------------------------------------------------

TestBTransform ==
    /\ bTransform(DepthM,1) = 1
    /\ bTransform(DepthM,2) = 2
    /\ bTransform(DepthM,3) = 4


\* ------------------------------------------------------------
\* eTransform
\* ------------------------------------------------------------

TestETransform ==
    /\ eTransform(DepthM,1) = 3
    /\ eTransform(DepthM,2) = 4
    /\ eTransform(DepthM,3) = 8


\* ------------------------------------------------------------
\* K
\* ------------------------------------------------------------

TestK ==
    LET
        KM == K(DepthM)
    IN
        /\ KM[1] = ExpectedL
        /\ KM[2] = ExpectedDerived


\* ============================================================
\* MW-CONSTRUCTION
\* ============================================================


\* ------------------------------------------------------------
\* min
\* ------------------------------------------------------------

TestMin ==
    /\ min(LeadM) = 1
    /\ min(
           <<Segment(2,6),
             Segment(2,3),
             Segment(5,8)>>
       ) = 2


\* ------------------------------------------------------------
\* LeadingSequence
\*
\* Unique chain:
\*
\*   [1,1] -> [2,2] -> [3,4]
\*
\* ------------------------------------------------------------

TestLeadingSequence ==
    LeadingSequence(LeadM) = <<1,2,3>>


\* ------------------------------------------------------------
\* IStar
\* ------------------------------------------------------------

TestIStar ==
    IStar(LeadM) = {1,2,3}


\* ------------------------------------------------------------
\* DeltaStar
\*
\* LeadM tests the THEN branch.
\* ShortLeadM index 2 tests the ELSE branch.
\* ------------------------------------------------------------

TestDeltaStar ==
    /\ DeltaStar(LeadM,1) = EmptySeg
    /\ DeltaStar(LeadM,2) = EmptySeg
    /\ DeltaStar(LeadM,3) = Segment(4,4)

    /\ DeltaStar(ShortLeadM,2)
           = Segment(2,2)


\* ------------------------------------------------------------
\* MCross
\*
\* The first two singleton segments disappear.
\* Only [3,4] -> [4,4] survives.
\* ------------------------------------------------------------

TestMCross ==
    MCross(LeadM) =
        <<Segment(4,4)>>


\* ------------------------------------------------------------
\* DeltaCircle
\*
\* min = 1
\* leading-sequence length = 3
\* therefore [1,3]
\* ------------------------------------------------------------

TestDeltaCircle ==
    DeltaCircle(LeadM) = Segment(1,3)


\* ------------------------------------------------------------
\* MW
\* ------------------------------------------------------------

TestMW ==
    LET
        X == MW(LeadM)
    IN
        /\ X[1] = <<Segment(4,4)>>
        /\ X[2] = Segment(1,3)


\* ============================================================
\* SECTION AGGREGATES
\* ============================================================

AllSegmentTests ==
    /\ TestSegment
    /\ TestSeg
    /\ TestEmptySeg
    /\ TestB
    /\ TestE
    /\ TestSegShiftLeft
    /\ TestSegTruncateLeft
    /\ TestPrecedes
    /\ TestSegSubsetEq


AllMultisegmentTests ==
    /\ TestMultisegments
    /\ TestSubMultisegment
    /\ TestSameMultisegment
    /\ TestIndexSet
    /\ TestDelta
    /\ TestIsLadder


AllDepthTests ==
    /\ TestDepth
    /\ TestD


AllKTests ==
    /\ TestDepthFiber
    /\ TestAdmissibleEnumeration
    /\ TestJIndex
    /\ TestIVee
    /\ TestSegmentTransform
    /\ TestDistinguishedIndices
    /\ TestRemainingIndices
    /\ TestL
    /\ TestDerivedMultisegment
    /\ TestBTransform
    /\ TestETransform
    /\ TestK


AllMWTests ==
    /\ TestMin
    /\ TestLeadingSequence
    /\ TestIStar
    /\ TestDeltaStar
    /\ TestMCross
    /\ TestDeltaCircle
    /\ TestMW


AllTests ==
    /\ AllSegmentTests
    /\ AllMultisegmentTests
    /\ AllDepthTests
    /\ AllKTests
    /\ AllMWTests


====