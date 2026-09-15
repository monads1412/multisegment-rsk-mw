include "segment.dfy"

module Utils{

    function Max(S: set<int>): int
        requires S != {}
    {
        var x: int :|
            x in S &&
            forall y: int :: y in S ==> y <= x;
        x
    }


    function SeqToSet(sequence : seq<int>): set<int> {
        set x: int | x in sequence
    }

    
}