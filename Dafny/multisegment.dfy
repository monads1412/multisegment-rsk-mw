include "segment.dfy"
include "utils.dfy"
module Multisegment{

    import opened Segment
    import opened Utils

    type Multisegment = seq<Segment>


    ghost predicate IsLadder(m : Multisegment){
        exists enumeration : Multisegment :: 
            multiset(enumeration) == multiset(m) &&         //multiset is a built-in function. initialization looks like: multiset{1, 2, 1, 3}
            |enumeration| == |m| &&
            forall index: int ::
                0 <= index < |m| - 1 ==>
                    Precedes(enumeration[index], enumeration[index + 1])
    }



    ghost function depth(i : int, m : Multisegment): int
        requires 0 <= i < |m|
    {
        MaxOf({0} + (set j: int | 0 <= j < |m| &&                   //{0} is artifically added because we need to satisfy the precondition of MaxOf which asserts that the set is nonempty
            exists s: seq<Segment> :: |s| == j + 1 && 
            multiset(s) <= multiset(m) && IsLadder(s) && s[0] == m[i]))
    }



    ghost function d(m : Multisegment): int
        requires |m| > 0
    {
        MaxOf({0} + (set index: int | 0 <= index < |m| :: depth(index, m)))
    }



    ghost function bucket(m : Multisegment, d : int): set<int>
    {
        set index: int | 0 <= index < |m| && depth(index, m) == d
    }



    ghost predicate IsAdmissible(m : Multisegment, k : int, enumeration : seq<int>)           //checks if a given sequence of indices constitutes an admissible enumeration of bucket(k)
        requires |m| > 0 && 0 <= k <= d(m)
    {
        SeqToSet(enumeration) == bucket(m, k)         //SeqToSet is a function from utils -- check if the enumeration indices are those of the bucket's
        && |enumeration| == |bucket(m, k)|              //making sure enumeration does not have duplicates
        && (forall j : int :: 0 <= j < |enumeration| ==> 0 <= enumeration[j] < |m|)     //making sure enumeration is a sequence of indices into m (none out-of-range)
        && (forall j : int :: 0 <= j < |enumeration| - 1 ==> Precedes(m[enumeration[j+1]], m[enumeration[j]]))
    }



    ghost function {:axiom} AdmissibleEnumeration(m : Multisegment, k : int): (e : seq<int>)  //a function with the following postconditions exists
        requires |m| > 0 && 0 <= k <= d(m)
        ensures IsAdmissible(m, k, AdmissibleEnumeration(m, k))



    ghost function IndexOf(e : seq<int>, x : int): int
        requires x in e
        decreases |e|
    {
        if e[0] == x then 0
        else 1 + IndexOf(e[1..], x)
    }


    //returns the position of the index i inside the admissible enumeration of its own depth bucket.
    ghost function {:axiom} Position(m : Multisegment, i : int): (p : int)
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
        ensures 0 <= p < |AdmissibleEnumeration(m, depth(i, m))|
        ensures AdmissibleEnumeration(m, depth(i, m))[p] == i



    ghost function IVee(m : Multisegment, i : int): (j : int)
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
        ensures 0 <= j < |m|
    {
        var e := AdmissibleEnumeration(m, depth(i, m));
        var p := Position(m, i);
        if p == |e| - 1 then e[0]
        else e[p+1]
    }



    lemma {:axiom} IVeeRange(m : Multisegment, i : int) 
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
        ensures 0 <= IVee(m, i) < |m|
        ensures m[i].0 <= m[IVee(m, i)].1



    ghost function TransformedSegment(m : Multisegment, i : int): Segment
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
    {
        IVeeRange(m, i);
        (m[i].0, m[IVee(m, i)].1)
    }



    lemma {:axiom} DepthExists(m : Multisegment, k : int)
        requires |m| > 0 && 0 <= k <= d(m)
        ensures exists i : int :: 0 <= i < |m| && depth(i, m) == k



    lemma AdmissibleEnumerationNonEmpty(m : Multisegment, k : int)
        requires |m| > 0 && 0 <= k <= d(m)
        ensures |AdmissibleEnumeration(m, k)| > 0
    {
        DepthExists(m, k);

        var i :| 0 <= i < |m| && depth(i, m) == k;

        assert i in bucket(m, k);
        assert |bucket(m, k)| > 0;

        var e := AdmissibleEnumeration(m, k);
        assert |e| == |bucket(m, k)|;
        assert |e| > 0;
    }



    ghost function j(m : Multisegment, k : int): int
        requires |m| > 0 && 0 <= k <= d(m)
    {
        AdmissibleEnumerationNonEmpty(m, k);
        var e := AdmissibleEnumeration(m, k);
        e[|e| - 1]
    }



    ghost function DistinguishedIndices(m : Multisegment): set<int>
        requires |m| > 0
    {
        set k : int | 0 <= k <= d(m) :: j(m, k)
    }



    ghost function RemainingIndices(m : Multisegment): set<int>
        requires |m| > 0
    {
        set k : int | 0 <= k < |m| && k !in DistinguishedIndices(m)
    }


    ghost function HighestLadderFrom(m : Multisegment, i : int): Multisegment
        requires 0 <= i <= |m| 
        decreases |m| - i
    {
        if i == |m| then []
        else if i in DistinguishedIndices(m) then
            [TransformedSegment(m, i)] + HighestLadderFrom(m, i + 1)
        else
            HighestLadderFrom(m, i + 1)
    }



    ghost function l(m : Multisegment): Multisegment
        requires |m| > 0
    {
        HighestLadderFrom(m, 0)
    }



    ghost function DerivedMultisegmentFrom(m : Multisegment, i : int): Multisegment
        requires 0 <= i <= |m|
        decreases |m| - i
    {
        if i == |m| then []
        else if i in RemainingIndices(m) then
            [TransformedSegment(m, i)] + DerivedMultisegmentFrom(m, i + 1)
        else
            DerivedMultisegmentFrom(m, i + 1)
    }



    ghost function DerivedMultisegment(m : Multisegment): Multisegment
        requires |m| > 0
    {
        DerivedMultisegmentFrom(m, 0)
    }



    ghost function K(m : Multisegment): seq<Multisegment>
        requires |m| > 0
        {
            [l(m), DerivedMultisegment(m)]
        }



    ghost predicate IsFirstLeadingIndex(m : Multisegment, i : int)
    {
        0 <= i < |m|
        && (forall r : int :: 0 <= r < |m| ==> m[i].0 <= m[r].0)
        && (forall r : int :: 0 <= r < |m| && m[r].0 == m[i].0 ==> m[i].1 <= m[r].1)
    }



    ghost function {:axiom} FirstLeadingIndex(m : Multisegment): (i : int)
        requires |m| > 0
        ensures IsFirstLeadingIndex(m, i)



    ghost function NextCandidates(m : Multisegment, current : int): set<int>
        requires 0 <= current < |m|
    {
        set i : int |
            0 <= i < |m|
            && Precedes(m[current], m[i])
            && m[i].0 == m[current].0 + 1
    }



    ghost function {:axiom} NextLeadingIndex(m : Multisegment, current : int): (next : int)
        requires 0 <= current < |m|
        requires NextCandidates(m, current) != {}
        ensures next in NextCandidates(m, current)
        ensures forall i : int :: i in NextCandidates(m, current) ==> m[next].1 <= m[i].1



    ghost function LeadingIndicesFrom(m : Multisegment, current : int, fuel : nat): seq<int>
        requires 0 <= current < |m|
        decreases fuel
    {
        if fuel == 0 || NextCandidates(m, current) == {} then []
        else
            var next := NextLeadingIndex(m, current);
            [next] + LeadingIndicesFrom(m, next, fuel - 1)
    }



    ghost function LeadingIndices(m : Multisegment): seq<int>
        requires |m| > 0
    {
        var i1 := FirstLeadingIndex(m);
        [i1] + LeadingIndicesFrom(m, i1, |m| - 1)
    }


    lemma LeadingIndicesNonEmpty(m : Multisegment)
        requires |m| > 0
        ensures |LeadingIndices(m)| > 0
    {
        var i1 := FirstLeadingIndex(m);
        assert i1 in LeadingIndices(m);
    }



    ghost function DeltaCircle(m : Multisegment): Segment
        requires |m| > 0
    {
        LeadingIndicesNonEmpty(m);
        var i1 := FirstLeadingIndex(m);
        (m[i1].0, m[i1].0 + |LeadingIndices(m)| - 1)
    }



    ghost function DeltaStar(m : Multisegment, i : int): Multisegment
        requires |m| > 0
        requires 0 <= i < |m|
    {
        if i in LeadingIndices(m) then
            if m[i].0 == m[i].1 then []
            else [(m[i].0 + 1, m[i].1)]
        else
            [m[i]]
    }



    ghost function MCrossFrom(m : Multisegment, i : int): Multisegment
        requires |m| > 0
        requires 0 <= i <= |m|
        decreases |m| - i
    {
        if i == |m| then []
        else DeltaStar(m, i) + MCrossFrom(m, i + 1)
    }



    ghost function MCross(m : Multisegment): Multisegment
        requires |m| > 0
    {
        MCrossFrom(m, 0)
    }



    ghost function MW(m : Multisegment): (Multisegment, Segment)
        requires |m| > 0
        {
            (MCross(m), DeltaCircle(m))
        }



    ghost function min(m : Multisegment): int
        requires |m| > 0
    {
        m[FirstLeadingIndex(m)].0
    }


    lemma {:axiom} Corollary(m : Multisegment)
        requires |m| > 0
        requires |l(m)| > 0
        requires min(m) < min(l(m))
        ensures
            |DerivedMultisegment(m)| > 0
            && |MCross(m)| > 0
            && l(m) == l(MCross(m))
            && DeltaCircle(m) == DeltaCircle(DerivedMultisegment(m))
            && DerivedMultisegment(MCross(m)) == MCross(DerivedMultisegment(m))
}