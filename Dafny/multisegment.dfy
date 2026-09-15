include "segment.dfy"
include "utils.dfy"
module Multisegment{

    import opened Segment
    import opened Utils

    type Multisegment = seq<Segment>


    ghost predicate IsLadder(m : Multisegment){
        exists enumeration : Multisegment :: 
            multiset(enumeration) == multiset(m) &&
            |enumeration| == |m| &&
            forall index: int ::
                0 <= index < |m| - 1 ==>
                    Precedes(enumeration[index], enumeration[index + 1])
    }


    ghost function depth(i : int, m : Multisegment): int
        requires 0 <= i < |m|
    {
        MaxOf({0} + (set j: int | 0 <= j < |m| &&
            exists s: seq<Segment> :: |s| == j + 1 && 
            multiset(s) <= multiset(m) && IsLadder(s) && s[0] == m[i]))
    }


    ghost function d(m : Multisegment): int
        requires |m| > 0
    {
        MaxOf({0} + (set index: int | 0 <= index < |m| :: depth(index, m)))
    }


    ghost function bucket(m : Multisegment, k : int): set<int>
        requires |m| > 0 && 0 <= k <= d(m)
    {
        set index: int | 0 <= index < |m| && depth(index, m) == k
    }


    ghost predicate IsAdmissibleEnumeration(m : Multisegment, k : int, enumeration : seq<int>)
        requires |m| > 0 && 0 <= k <= d(m)
    {
        SeqToSet(enumeration) == bucket(m, k)
        && (forall index : int :: 0 <= index < |enumeration| - 1 ==>
            0 <= enumeration[index] < |m| &&
            0 <= enumeration[index+1] < |m| &&
            Precedes(m[enumeration[index+1]], m[enumeration[index]]))
    }

    ghost function {:axiom} AdmissibleEnumeration(m : Multisegment, k : int): (enumeration : seq<int>)
        requires |m| > 0 && 0 <= k <= d(m)
        ensures IsAdmissibleEnumeration(m, k, enumeration)

}