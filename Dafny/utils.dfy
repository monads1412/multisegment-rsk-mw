module Utils{

    ghost function MaxOf(S: set<int>): int
        requires S != {}
    {
        var x : int :| x in S;
        if S == {x} then x
        else
            var m := MaxOf(S - {x});
            if x > m then x else m
    }


    function SeqToSet(sequence : seq<int>): set<int> {
        set x: int | x in sequence
    }

    
}