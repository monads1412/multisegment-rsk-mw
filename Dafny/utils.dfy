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



    ghost function SetToSequence(s : set<int>): seq<int>
        ensures forall x :: x in s <==> x in SetToSequence(s)
        decreases |s|
    {
        if s == {} then
            []
        else
            var x :| x in s;
            [x] + SetToSequence(s - {x})
    }



    /* non-ghost implementation of MaxOf -- function by method:

    function MaxOf(s: set<int>): (m: int)
    requires s != {}
    ensures m in s && forall z :: z in s ==> z <= m
    {
    var x :| x in s;
    if s == {x} then
        x
    else
        var s' := s - {x};
        assert s == s' + {x};
        var y := MaxOf(s');
        if x >= y then x else y
    } by method {
    m :| m in s;
    var r := s - {m};
    while r != {}
        invariant r < s
        invariant m in s && forall z :: z in s - r ==> z <= m
    {
        var x :| x in r;
        assert forall z :: z in s - (r - {x}) ==> z in s - r || z == x;
        r := r - {x};
        if m < x {
        m := x;
        }
    }
    assert s - {} == s;
    }


    */ 
}