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


    function d(m : Multisegment): int
        requires |m| > 0
    {
        max(set index: int | 0 <= index < |m| :: depth(index, m))
    }


    function bucket(m : Multisegment, k : int): set<int>
        requires 0 <= k <= d(m)
    {
        set index: int | 0 <= index < |m| && depth(index, m) == k
    }

    function AdmissibleEnumeration(m : Multisegment, k : int): seq<int>
        requires |m| > 0 && 0 <= k <= d(m)
        {
            var enumeration : seq<int> :| 
                    SeqToSet(enumeration) == bucket(m, k)
                    && (forall index: int :: 0 <= index < |enumeration| - 1 ==> 
                        Precedes(m[enumeration[index+1]], m[enumeration[index]]));
            enumeration
        }

}