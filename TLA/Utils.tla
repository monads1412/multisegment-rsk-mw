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


Enumerations(S) ==
    {P \in [1..Cardinality(S) -> S] :
        IsInjective(P)}                                      \* all enumerations/permutations of finite S


ChoosePermutation(S) ==
    CHOOSE P \in Enumerations(S) :
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


SubMultiset(A, B) ==
    \A x \in Range(A) :
        Multiplicity(A, x) <= Multiplicity(B, x)             \* every value occurs at most as often in A as in B


SameBag(A, B) ==
    /\ SubMultiset(A, B)
    /\ SubMultiset(B, A)                                         \* A and B contain the same values with the same multiplicities


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
