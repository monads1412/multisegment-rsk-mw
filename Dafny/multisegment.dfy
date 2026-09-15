include "segment.dfy"
include "utils.dfy"
module Multisegment{

    type Multisegment = seq<Segment>


    predicate IsLadder(m : Multisegment){
        exists enumeration : multisegment :: 
            multiset(enumeration) = multiset(m) &&
            forall index: int ::
                0 <= index < |m| - 1 ==>
                    Precedes(enumeration[index], enumeration[index + 1])
    }


    function depth(i : int, m : Multisegment): int
        requires 0 <= i < |m|
    {
        max(set s: seq<int> | |s| > 0 && multiset(s) <= multiset(m) && IsLadder(m) && s[0] = m[i] :: |s|-1)
    }

//exists a submultisegment such that the first element is m[i] and m is a ladder
}