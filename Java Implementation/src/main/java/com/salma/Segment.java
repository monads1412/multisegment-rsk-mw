package com.salma;
import java.util.Set;
import java.util.HashSet; 

public class Segment implements Comparable<Segment> {
    public final int b;
    public final int e;

    public Segment(int x, int y){
        this.b = x;
        this.e = y;

    }

    // check if s is a valid segment //
    public boolean isSegment(Segment s){
        return s.b <= s.e;
    }
    
    // turn the segment into an actual set - not sure if it is needed, can delete later//
    public Set<Integer> segmentToSet(Segment s){
        Set<Integer> x = new HashSet<>();
        for (int i = s.b; i <= s.e; i++){
            x.add(i);
        }
        return x;
    }

    public boolean precedes(Segment s2){
        return isSegment(this) && isSegment(s2) && this.b < s2.b && this.e < s2.e;
    }

    //check if used at all (probably not)
    public boolean subsetEq(Segment s1, Segment s2){
        return isSegment(s1) && isSegment(s2) && s1.b <= s2.b && s2.e <= s1.e;
    }

    // compare two segments: first b1 < b2, then e2 < e1
    @Override
    public int compareTo(Segment other) {
        if (this.b != other.b) {
            return Integer.compare(this.b, other.b);
        }

        return Integer.compare(other.e, this.e);
    }
}