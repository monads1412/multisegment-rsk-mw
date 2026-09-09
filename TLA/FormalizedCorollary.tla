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
    SubBag(N, M)


SameMultisegment(M, N) ==
    SameBag(M, N)


IndexSet(M) ==
    1..Len(M)

Delta(M) == M                                               \* sticking to paper notation (redundant)

IsLadder(M) ==
    /\ M # <<>>                                              \* a ladder is nonempty
    /\ \E R \in Permutations(IndexSet(M)) :
        \A i \in 1..(Len(M) - 1) :
            Precedes(M[R[i + 1]], M[R[i]])                   \* Delta_{R[i+1]} ≺ Delta_{R[i]}                                

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


AdmissibleEnumeration(m, k) ==
    LET
        F == DepthFiber(m, k)                                \* depth fiber at k

        IsAdmissible(P) ==
            \A r \in 1..(Cardinality(F) - 1) :
                SegSubsetEq(
                    Delta(m)[P[r + 1]],
                    Delta(m)[P[r]]
                )                                            \* P satisfies the admissibility condition
    IN
        CHOOSE P \in Permutations(F) :
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
        PermutationFromCycles(
            IndexSet(M),
            Cycles
        )                                                    \* permutation i |-> i^vee induced by these cycles


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



============================================================================
Glossary
============================================================================

Segment
constructs the sequence <<a, b>> (keeping in mind that a sequence is a
function from indexes to values of the sequence).
why choose a sequence and not a set?
because what we mainly use and care about in the proof are the endpoints.

Seg
the set of all valid segments [a,b] with a <= b.

EmptySeg
the empty sequence <<>>, which we use to represent the empty segment.
EmptySeg is not part of Seg.

b(s)
returns the beginning/left endpoint of a segment s.
if s = <<a,b>>, then b(s)=a.

e(s)
returns the ending/right endpoint of a segment s.
if s = <<a,b>>, then e(s)=b.

SegShiftLeft(s)
shifts both endpoints of a segment one place to the left.
[a,b] becomes [a-1,b-1].

SegTruncateLeft(s)
removes the left endpoint of a segment.
if the segment is [a,b] with a<b, it returns [a+1,b].
if the segment is a singleton [a,a], it returns EmptySeg.

Precedes(s1,s2)
checks whether s1 ≺ s2.
this means that both the beginning and the ending of s1 are strictly
smaller than those of s2.

SegSubsetEq(s1,s2)
checks whether s1 is contained in s2, including equality.
for s1=[a1,b1] and s2=[a2,b2], this means
a2 <= a1 and b1 <= b2.


Multisegments
the set of all multisegments, which are sequences of segments.
why choose sequences of segments and not multisets/bags of segments?
because we need to easily be able to use the indexes of the segments,
even with repetition.

this means that two different sequences may represent the same
mathematical multisegment. we deal with this using SameMultisegment
rather than ordinary sequence equality.

SubMultisegment(N,M)
checks whether N is a submultisegment of M.
internally, this is SubBag(N,M), meaning that every segment occurring in N
occurs in M at least as many times.

SameMultisegment(M,N)
checks whether M and N represent the same mathematical multisegment,
even if they are different sequences.
internally, this is SameBag(M,N), so equality is determined by the
segments and their multiplicities and not by their order.

IndexSet(M)
returns the set 1..Len(M), i.e. the set of global indexes of the segments
in M.

Delta(M)
returns the function i |-> Delta_i, where Delta_i is the segment at
global index i.
since M itself is a sequence, this is extensionally the same function
as M, but we keep Delta(M) in order to stay close to the notation
of the paper.

IsLadder(M)
checks whether M is a ladder.
first, M must be nonempty.
then there must exist a permutation R of IndexSet(M) such that the
segments are in standard form, i.e.
Delta_{R[i+1]} ≺ Delta_{R[i]} for every successive pair.
using Permutations here already makes sure that R contains every
global index exactly once.


Depth(M)
returns the function i |-> d_M(i), where d_M(i) is the depth of the
segment at index i.
it does this by taking the maximum j such that there exists a depth chain
of length j starting at index i.

internally, IsDepthChain(i,j,Chain) checks that Chain[1]=i and that
for every r in [j],
Delta_{Chain[r]} ≺ Delta_{Chain[r+1]}.
we do not define IsDepthChain as an outer operator because it is only
auxiliary machinery needed for defining Depth.

d(M)
returns the depth of the multisegment M.
if M is empty it returns 0.
otherwise, it takes the maximum value in Range(Depth(M)).


DepthFiber(M,k)
returns the depth fiber d_M^(-1)(k), i.e. the set of indexes i such that
Depth(M)[i]=k.
this is implemented using the general Fiber operator.

AdmissibleEnumeration(m,k)
chooses an admissible enumeration of the depth fiber at k.
it first sets F to DepthFiber(m,k), and then chooses a permutation P of F
such that Delta_{P[r+1]} is contained in Delta_{P[r]} for every
successive pair.
we do not impose any canonical ordering: CHOOSE simply selects one
admissible enumeration.

jIndex(M,k)
returns j_k, i.e. the last index in the chosen admissible enumeration
at depth k.
if k is not a depth occurring in M, it returns 0.
the last element is obtained using the general Last operator.

IVee(M)
returns the permutation i |-> i^vee.
for each depth, the chosen admissible enumeration is treated as a cycle.
the set of these cycles is then passed to the general
PermutationFromCycles operator.

SegmentTransform(M,i)
returns Delta'_i.
its beginning is b(Delta_i), while its ending is e(Delta_{i^vee}).

DistinguishedIndices(M)
returns the set I' of distinguished indexes j_k,
one for every depth occurring in M.

RemainingIndices(M)
returns I'' = I \ I', i.e. the global indexes that are not distinguished.

l(M)
returns the ladder l(m).
for each depth r-1 from 0 to d(M), it takes the transformed segment
Delta'_{j_{r-1}}.

DerivedMultisegment(M)
returns m', the multisegment consisting of Delta'_i for all i in I''.
since a multisegment is represented by a sequence, we need some
enumeration of these values.
this is handled by the general EnumerateValues operator rather than being
built directly into this paper-specific definition.

K(M)
returns <<l(M), DerivedMultisegment(M)>>,
i.e. K(m) = (l(m),m').


min(M)
returns min m, i.e. the smallest beginning among all segments of M.
this is implemented by taking Min of the set of all b(Delta_i).

LeadingSequence(M)
chooses a sequence <<i_1,...,i_k>> satisfying 3.1a-3.1c.

internally, CandidateSequences contains all possible nonempty sequences
of indexes of length at most Len(M).

FirstOK(i) checks 3.1a:
Delta_i begins at min(M), and among all segments beginning there it has
minimal ending.

NextCandidate(i,q) checks whether q can follow i:
Delta_i ≺ Delta_q and b(Delta_q)=b(Delta_i)+1.

NextOK(i,next) checks 3.1b:
next is a valid candidate, and among all valid candidates it has
minimal ending.

IsValid(S) checks that the first element satisfies FirstOK,
every successive pair satisfies NextOK, and that there is no valid
successor after the last element, which gives 3.1c.

CHOOSE then selects one complete leading sequence.
these auxiliary operators are local because they are only machinery
for implementing the recursive construction described in the paper.

IStar(M)
returns I* = {i_1,...,i_k}, the set of indexes occurring in the chosen
leading sequence.
this is simply Range(LeadingSequence(M)).

DeltaStar(M,i)
returns Delta_i*.
if i is in I*, it applies SegTruncateLeft to Delta_i.
otherwise, it leaves Delta_i unchanged.

MCross(M)
returns m^cross.
first it keeps exactly those indexes for which Delta_i* is not EmptySeg.
it then uses EnumerateValues to turn the surviving transformed segments
into a sequence.
therefore empty transformed segments are discarded, while repetitions
of nonempty segments are preserved.

DeltaCircle(M)
returns Delta^circle.
if the chosen leading sequence has length k, then
Delta^circle = [min(M), min(M)+k-1].

MW(M)
returns <<MCross(M), DeltaCircle(M)>>,
i.e. MW(m) = (m^cross,Delta^circle).


============================================================================
Utils
============================================================================

Range(f)
returns the image/range of a function f,
i.e. {f[x] : x \in DOMAIN f}.

Max(S)
returns the maximum element of a nonempty finite set S.

Min(S)
returns the minimum element of a nonempty finite set S.

IsInjective(f)
checks whether f is injective:
distinct elements of DOMAIN f must have distinct images.

Permutations(S)
returns the set of all permutations of a finite set S.
a permutation is represented as a function from 1..Cardinality(S) to S
which is injective.
because the domain and S have the same finite cardinality,
injectivity also guarantees that every element of S occurs exactly once.

ChoosePermutation(S)
chooses one arbitrary permutation of S using CHOOSE.
this is useful whenever we need to turn a set of indexes into a sequence
but do not care about the particular order.

Fiber(f,y)
returns the fiber/preimage of y under f,
i.e. all x in DOMAIN f such that f[x]=y.

Last(S)
returns the last element of a nonempty sequence S,
i.e. S[Len(S)].

Multiplicity(S,x)
returns the number of indexes i for which S[i]=x.
when S represents a bag/multiset, this is the multiplicity of x
in that bag.

SubBag(A,B)
checks whether A is a subbag of B.
for every value occurring in A, its multiplicity in A must be no greater
than its multiplicity in B.

SameBag(A,B)
checks whether A and B represent the same bag.
this means SubBag(A,B) and SubBag(B,A), so order is ignored but
repetitions/multiplicities are preserved.

PermutationFromCycles(I,Cycles)
constructs a permutation of I from a set of cycles.
for each i, it finds the cycle E containing i and the position r of i in E.
if i is the last element of E, it maps i to E[1].
otherwise, it maps i to E[r+1].

EnumerateValues(f)
turns the values of a finite function f into a sequence.
it chooses a permutation of DOMAIN f and returns the values of f in
that order.
unlike Range(f), this preserves repetitions:
if two different indexes map to the same value, that value appears twice
in the resulting sequence.


============================================================================
Notes on notation and organization
============================================================================

why choose operators and not function notations?
for instance, why define Multiplicity as Multiplicity(S,x) without
specifying the domain, meaning something like
Multiplicity[S \in Seq(...), x \in ...]?

TLA+ is untyped, so if we do need to specify the domain, we can do so in
the definitions that use these objects.
second, the bracket notation defines a function, while the operator
notation defines an operator.
from a more practical standpoint, unfolding the operator notation in a
proof requires less machinery and less proof obligations.



the purpose of Utils is to separate operations that are not specific to
this paper, such as Range, Fiber, permutations, bag equality, or
constructing a permutation from cycles.



