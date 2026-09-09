---- MODULE Utils ----
EXTENDS Integers, FiniteSets, Sequences


Range(f) ==
    {f[x] : x \in DOMAIN f}                                  \* image/range of f


Max(S) ==
    CHOOSE x \in S :
        \A y \in S :
            x >= y                                           \* maximum element of nonempty S


Min(S) ==
    CHOOSE x \in S :
        \A y \in S :
            x <= y                                           \* minimum element of nonempty S


IsInjective(f) ==
    \A x, y \in DOMAIN f :
        x # y => f[x] # f[y]                                 \* distinct inputs have distinct outputs


Permutations(S) ==
    {P \in [1..Cardinality(S) -> S] :
        IsInjective(P)}                                      \* all enumerations/permutations of finite S


ChoosePermutation(S) ==
    CHOOSE P \in Permutations(S) :
        TRUE                                                 \* choose an arbitrary permutation of S


Fiber(f, y) ==
    {x \in DOMAIN f :
        f[x] = y}                                            \* preimage of y under f


Last(S) ==
    S[Len(S)]                                                \* last element of a nonempty sequence


Multiplicity(S, x) ==
    Cardinality(
        {i \in DOMAIN S :
            S[i] = x}
    )                                                        \* number of occurrences of x in sequence S


SubBag(A, B) ==
    \A x \in Range(A) :
        Multiplicity(A, x) <= Multiplicity(B, x)             \* every value occurs at most as often in A as in B


SameBag(A, B) ==
    /\ SubBag(A, B)
    /\ SubBag(B, A)                                         \* A and B contain the same values with the same multiplicities


PermutationFromCycles(I, Cycles) ==                         \* Cycles is meant to be a set of tuples of integers    
    [i \in I |->
        LET
            E ==
                CHOOSE E \in Cycles :
                    i \in Range(E)

            r ==
                CHOOSE p \in 1..Len(E) :                    \* finds the index of i in the subcycle E
                    E[p] = i

        IN
            IF r = Len(E)
            THEN E[1]
            ELSE E[r + 1]
    ]

EnumerateValues(f) ==                                       \* takes a finite function f and turns its values into a sequence
    LET
        E == ChoosePermutation(DOMAIN f)                    \* choose an ordering of the domain
    IN
        [r \in 1..Cardinality(DOMAIN f) |->
            f[E[r]]]                                        \* enumerate the values of f with multiplicity



============================================================================
Utils Glossary
============================================================================

Range(f)
returns the image/range of a function f,
i.e. {f[x] : x \in DOMAIN f}.

Max(S)
returns the maximum element of a nonempty finite set S.
it uses CHOOSE to select an x in S such that x >= y
for every y in S.

Min(S)
returns the minimum element of a nonempty finite set S.
it uses CHOOSE to select an x in S such that x <= y
for every y in S.

IsInjective(f)
checks whether f is injective.
for every two distinct elements x and y in DOMAIN f,
their images f[x] and f[y] must also be distinct.

Permutations(S)
returns the set of all permutations of a finite set S.
a permutation P is represented as a function from
1..Cardinality(S) to S.

we require P to be injective.
since its domain and S have the same finite cardinality,
injectivity also guarantees surjectivity, so every element
of S occurs exactly once.

ChoosePermutation(S)
chooses one arbitrary permutation of S from Permutations(S).

we use this when we need to represent the elements of a set
as a sequence but do not care about which particular ordering
is chosen.

the choice is made using CHOOSE, so it is unspecified but
not intended to represent a random choice every time the
operator is evaluated.

Fiber(f,y)
returns the fiber/preimage of y under f,
i.e. the set of all x in DOMAIN f such that f[x]=y.

for example, in Final we use
Fiber(Depth(M),k)
to represent the depth fiber d_M^(-1)(k).

Last(S)
returns the last element of a nonempty sequence S,
i.e. S[Len(S)].

Multiplicity(S,x)
returns the number of times x occurs as a value of S.

it does this by collecting all indexes i in DOMAIN S
such that S[i]=x, and taking the cardinality of this set.

this is especially useful when a sequence is being used
to represent a bag/multiset.

SubBag(A,B)
checks whether A is a subbag of B.

for every value x occurring in A,
the multiplicity of x in A must be no greater than
the multiplicity of x in B.

the ordering of the elements is therefore irrelevant,
while repetitions are taken into account.

SameBag(A,B)
checks whether A and B represent the same bag/multiset.

it checks both
SubBag(A,B)
and
SubBag(B,A).

therefore A and B may be different sequences in terms of order,
but SameBag(A,B) is true exactly when they contain the same
values with the same multiplicities.

PermutationFromCycles(I,Cycles)
constructs the permutation of I induced by a collection of cycles.

for each i in I, it first chooses the cycle E containing i.
it then finds the position r of i in E.

if i is the last element of E, it maps i to E[1].
otherwise, it maps i to E[r+1].

so a cycle such as

<<1,3,2>>

induces the mappings

1 |-> 3
3 |-> 2
2 |-> 1.

this operator is general and not specific to the paper.
in Final we use it to construct the permutation i |-> i^vee
from the admissible enumerations of the depth fibers.

EnumerateValues(f)
turns the values of a finite function f into a sequence.

it first chooses a permutation E of DOMAIN f.
it then returns the sequence

<<f[E[1]], ..., f[E[n]]>>

where n = Cardinality(DOMAIN f).

the particular ordering is irrelevant.

unlike Range(f), EnumerateValues(f) preserves repetitions.
if two different elements of DOMAIN f map to the same value,
that value occurs twice in the resulting sequence.

this is why we use EnumerateValues rather than Range when
constructing multisegments: a multisegment may contain
multiple copies of the same segment.
