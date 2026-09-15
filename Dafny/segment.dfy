module Segment{
               
    // defining the type Segment
    type Segment = s : (int, int) | s.0 <= s.1 witness (0, 0)


    method ShiftLeft(s : Segment) returns (s2 : Segment) {
        s2 := (s.0 - 1, s.1 - 1);
    }


    method TruncateLeft(s : Segment) returns (s2 : Segment) 
        requires s.0 < s.1
    {
        s2 := (s.0 + 1, s.1);
    }


    predicate Precedes(s1 : Segment, s2 : Segment){
        s1.0 < s2.0 && s1.1 < s2.1
    }


    predicate SegSubsetEq(s1 : Segment, s2 : Segment){
        s1.0 <= s2.0 && s2.1 <= s1.1
    }
 
 
}