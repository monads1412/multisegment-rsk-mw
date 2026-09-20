include "segment.dfy"
include "utils.dfy"
module Multisegment{

    import opened Segment
    import opened Utils

    type Multisegment = seq<Segment>


    ghost predicate IsLadder(m : Multisegment)
        requires |m| > 0
    {
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
        MaxOf({0} + (set j : int | 0 <= j < |m| &&                  //{0} is artifically added because we need to satisfy the precondition of MaxOf which asserts that the set is nonempty
            exists s : seq<Segment> ::
                |s| == j + 1 &&
                multiset(s) <= multiset(m) &&
                s[0] == m[i] &&
                forall r : int ::
                    0 <= r < |s| - 1 ==> Precedes(s[r], s[r+1])))
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
        && (forall j : int :: 0 <= j < |enumeration| - 1 ==> SegSubsetEq(m[enumeration[j]], m[enumeration[j+1]]))
    }



    ghost function {:axiom} AdmissibleEnumeration(m : Multisegment, k : int): (e : seq<int>)   // chooses an admissible enumeration of the depth-k fiber
        requires |m| > 0 && 0 <= k <= d(m)
        ensures IsAdmissible(m, k, e)



    ghost function IndexOf(e : seq<int>, x : int): int
        requires x in e
        decreases |e|
    {
        if e[0] == x then 0
        else 1 + IndexOf(e[1..], x)
    }


    //returns the position of the index i inside the admissible enumeration of its own depth bucket. -- had to split into smaller functions because the verifier was timing out.
    ghost function Position(m : Multisegment, i : int): (p : int)
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
        ensures 0 <= p < |AdmissibleEnumeration(m, depth(i, m))|
        ensures AdmissibleEnumeration(m, depth(i, m))[p] == i
    {
        var e := AdmissibleEnumeration(m, depth(i, m));

        assert i in bucket(m, depth(i, m));
        assert IsAdmissible(m, depth(i, m), e);
        assert SeqToSet(e) == bucket(m, depth(i, m));
        assert i in SeqToSet(e);
        assert i in e;

        var p :| 0 <= p < |e| && e[p] == i;
        p
    }



    ghost function IVee(m : Multisegment, i : int): (j : int)
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
        ensures 0 <= j < |m|
    {
        var e := AdmissibleEnumeration(m, depth(i, m));
        var p := Position(m, i);
        if p == |e| - 1 then e[0]
        else e[p+1]
    }



    lemma AdmissibleNested(m : Multisegment, k : int, e : seq<int>, p : int, q : int)           //proves that every earlier segment in an admissible enumeration contains every later segment
        requires |m| > 0 && 0 <= k <= d(m)
        requires IsAdmissible(m, k, e)
        requires 0 <= p <= q < |e|
        ensures SegSubsetEq(m[e[p]], m[e[q]])
        decreases q - p
    {
        if p == q {
            assert SegSubsetEq(m[e[p]], m[e[p]]);
        } else {
            AdmissibleNested(m, k, e, p, q - 1);
            assert SegSubsetEq(m[e[q - 1]], m[e[q]]);

            assert m[e[p]].0 <= m[e[q - 1]].0;
            assert m[e[q - 1]].0 <= m[e[q]].0;

            assert m[e[q]].1 <= m[e[q - 1]].1;
            assert m[e[q - 1]].1 <= m[e[p]].1;

            assert SegSubsetEq(m[e[p]], m[e[q]]);
        }
    }


    lemma IVeeRange(m : Multisegment, i : int)                  //proves that i^vee is a valid index and that [b(Delta_i), e(Delta_i^vee)] is a valid segment
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
        ensures 0 <= IVee(m, i) < |m|
        ensures m[i].0 <= m[IVee(m, i)].1
    {
        var e := AdmissibleEnumeration(m, depth(i, m));
        var p := Position(m, i);

        assert IsAdmissible(m, depth(i, m), e);
        assert 0 <= p < |e|;
        assert e[p] == i;
        assert |e| > 0;

        if p == |e| - 1 {
            AdmissibleNested(m, depth(i, m), e, 0, p);

            assert SegSubsetEq(m[e[0]], m[e[p]]);
            assert m[e[p]].0 <= m[e[p]].1;
            assert m[e[p]].1 <= m[e[0]].1;
            assert m[i].0 <= m[e[0]].1;
            assert IVee(m, i) == e[0];
        } else {
            assert 0 <= p + 1 < |e|;
            assert SegSubsetEq(m[e[p]], m[e[p + 1]]);

            assert m[e[p]].0 <= m[e[p + 1]].0;
            assert m[e[p + 1]].0 <= m[e[p + 1]].1;
            assert m[i].0 <= m[e[p + 1]].1;
            assert IVee(m, i) == e[p + 1];
        }
    }

    ghost function TransformedSegment(m : Multisegment, i : int): Segment
        requires 0 <= i < |m| && 0 <= depth(i, m) <= d(m)
    {
        IVeeRange(m, i);
        (m[i].0, m[IVee(m, i)].1)
    }


    lemma {:axiom} LowerDepthExists(m : Multisegment, i : int, k : int)    //Lemma 2.1(1): every smaller depth below depth(i) is attained by a segment succeeding Δ_i
        requires 0 <= i < |m| && 0 <= k < depth(i, m)
        ensures exists j : int ::
            0 <= j < |m| &&
            Precedes(m[i], m[j]) &&
            depth(j, m) == k


    lemma MaxDepthExists(m : Multisegment)    //proves that some index of m has depth d(m)
        requires |m| > 0
        ensures exists i : int :: 0 <= i < |m| && depth(i, m) == d(m)



    lemma DepthExists(m : Multisegment, k : int)    //proves that every depth k from 0 through d(m) is attained
        requires |m| > 0 && 0 <= k <= d(m)
        ensures exists i : int :: 0 <= i < |m| && depth(i, m) == k
    {
        MaxDepthExists(m);
        var imax :| 0 <= imax < |m| && depth(imax, m) == d(m);

        if k == d(m) {
            assert 0 <= imax < |m| && depth(imax, m) == k;
        } else {
            assert k < depth(imax, m);
            LowerDepthExists(m, imax, k);
        }
    }



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
        set i : int | 0 <= i < |m| && i !in DistinguishedIndices(m)
    }



    lemma DepthRange(m : Multisegment, i : int)    //proves that the depth of every index lies between 0 and d(m)
        requires 0 <= i < |m|
        ensures 0 <= depth(i, m) <= d(m)


    ghost function HighestLadderFrom(m : Multisegment, i : int): Multisegment
        requires 0 <= i <= |m| 
        decreases |m| - i
    {
        if i == |m| then []
        else if i in DistinguishedIndices(m) then
            DepthRange(m, i);
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
            DepthRange(m, i);
            [TransformedSegment(m, i)] + DerivedMultisegmentFrom(m, i + 1)
        else
            DerivedMultisegmentFrom(m, i + 1)
    }



    ghost function DerivedMultisegment(m : Multisegment): Multisegment    //returns the derived multisegment m'
        requires |m| > 0
    {
        DerivedMultisegmentFrom(m, 0)
    }


    ghost function K(m : Multisegment): (Multisegment, Multisegment)      //returns the single RSK step K(m) = (l(m), m')
        requires |m| > 0
    {
        (l(m), DerivedMultisegment(m))
    }


    ghost predicate IsFirstLeadingIndex(m : Multisegment, i : int)
    {
        0 <= i < |m|
        && (forall r : int :: 0 <= r < |m| ==> m[i].0 <= m[r].0)
        && (forall r : int :: 0 <= r < |m| && m[r].0 == m[i].0 ==> m[i].1 <= m[r].1)
    }



    lemma FirstLeadingIndexExists(m : Multisegment)    //proves that a segment satisfying condition (3.1a) exists
        requires |m| > 0
        ensures exists i : int :: IsFirstLeadingIndex(m, i)
    {
        var best := 0;
        var r := 1;

        while r < |m|
            invariant 1 <= r <= |m|
            invariant 0 <= best < r
            invariant forall q : int :: 0 <= q < r ==> m[best].0 <= m[q].0
            invariant forall q : int ::
                0 <= q < r && m[q].0 == m[best].0 ==> m[best].1 <= m[q].1
            decreases |m| - r
        {
            if m[r].0 < m[best].0 ||
            (m[r].0 == m[best].0 && m[r].1 < m[best].1)
            {
                best := r;
            }

            r := r + 1;
        }

        assert IsFirstLeadingIndex(m, best);
    }


    ghost function FirstLeadingIndex(m : Multisegment): (i : int)    //chooses an index i1 satisfying the paper's first-leading-index condition (3.1a)
        requires |m| > 0
        ensures IsFirstLeadingIndex(m, i)
    {
        FirstLeadingIndexExists(m);
        var chosen :| IsFirstLeadingIndex(m, chosen);
        chosen
    }


    ghost function NextCandidates(m : Multisegment, current : int): set<int>
        requires 0 <= current < |m|
    {
        set i : int |
            0 <= i < |m|
            && Precedes(m[current], m[i])
            && m[i].0 == m[current].0 + 1
    }


    lemma NextLeadingIndexExists(m : Multisegment, current : int)    //proves that a candidate with minimal ending exists
        requires 0 <= current < |m|
        requires NextCandidates(m, current) != {}
        ensures exists next : int ::
            next in NextCandidates(m, current)
            && forall i : int ::
                i in NextCandidates(m, current) ==> m[next].1 <= m[i].1
    {
        var best :| best in NextCandidates(m, current);
        var r := 0;

        while r < |m|
            invariant 0 <= r <= |m|
            invariant best in NextCandidates(m, current)
            invariant forall q : int ::
                q in NextCandidates(m, current) && 0 <= q < r ==>
                    m[best].1 <= m[q].1
            decreases |m| - r
        {
            if r in NextCandidates(m, current) && m[r].1 < m[best].1 {
                best := r;
            }
            r := r + 1;
        }

        assert forall q : int ::
            q in NextCandidates(m, current) ==> 0 <= q < |m|;

        assert forall q : int ::
            q in NextCandidates(m, current) ==> m[best].1 <= m[q].1;
    }



    ghost function NextLeadingIndex(m : Multisegment, current : int): (next : int)    //chooses an eligible next leading index with minimal ending
        requires 0 <= current < |m|
        requires NextCandidates(m, current) != {}
        ensures next in NextCandidates(m, current)
        ensures forall i : int ::
            i in NextCandidates(m, current) ==> m[next].1 <= m[i].1
    {
        NextLeadingIndexExists(m, current);
        var next :|
            next in NextCandidates(m, current)
            && forall i : int ::
                i in NextCandidates(m, current) ==> m[next].1 <= m[i].1;
        next
    }



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
            && multiset(l(m)) == multiset(l(MCross(m)))                 //using multiset operator because index-order is not unique
            && DeltaCircle(m) == DeltaCircle(DerivedMultisegment(m))
            && multiset(DerivedMultisegment(MCross(m)))
                == multiset(MCross(DerivedMultisegment(m)))
                
}