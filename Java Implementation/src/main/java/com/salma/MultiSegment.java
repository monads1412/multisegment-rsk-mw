package com.salma;

import java.util.*;

import com.google.common.collect.Multiset;
import com.google.common.collect.SortedMultiset;
import com.google.common.collect.TreeMultiset;

public class MultiSegment {

    /*
     * The multisegment itself.
     * This is the only thing constructed immediately.
     */
    private final SortedMultiset<Segment> ms;


    /*
     * Lazily computed derived information.
     *
     * These remain null until some operation actually needs them.
     */
    private List<Segment> distinctSegments = null;
    private List<Integer> cumulativeFreq = null;
    private int[] longestStarting = null;
    private List<List<Integer>> admissibleEnumerations = null;


    public MultiSegment(Segment... segments) {

        ms = TreeMultiset.create();
        ms.addAll(Arrays.asList(segments));
    }


    /*
     * Computes the distinct segments and cumulative frequencies
     * only when they are first needed.
     */
    private void buildDistinctData() {

        if (distinctSegments != null) {
            return;
        }

        distinctSegments = new ArrayList<>();
        cumulativeFreq = new ArrayList<>();

        int cumulative = 0;

        for (Multiset.Entry<Segment> entry : ms.entrySet()) {

            distinctSegments.add(entry.getElement());

            cumulative += entry.getCount();
            cumulativeFreq.add(cumulative);
        }
    }


    private List<Segment> distinctSegments() {

        buildDistinctData();

        return distinctSegments;
    }


    private List<Integer> cumulativeFreq() {

        buildDistinctData();

        return cumulativeFreq;
    }


    /*
     * Computes, for every distinct segment, the length of a
     * longest precedence chain starting at that segment.
     *
     * Since segments are ordered by b ascending, if s1 precedes s2,
     * then s2 must occur after s1.
     *
     * Therefore we process the distinct segments from right to left.
     *
     * Time complexity: O(d^2), where d is the number
     * of distinct segments.
     */
    private int[] longestStarting() {

        if (longestStarting != null) {
            return longestStarting;
        }

        List<Segment> distinct = distinctSegments();

        int n = distinct.size();

        longestStarting = new int[n];

        for (int i = n - 1; i >= 0; i--) {

            longestStarting[i] = 1;

            for (int j = i + 1; j < n; j++) {

                Segment current = distinct.get(i);
                Segment next = distinct.get(j);

                if (current.precedes(next)) {

                    longestStarting[i] =
                        Math.max(
                            longestStarting[i],
                            1 + longestStarting[j]
                        );
                }
            }
        }

        return longestStarting;
    }


    /*
     * Builds an admissible enumeration of every depth fiber d^{-1}(k).
     *
     * The entries are indices in the expanded sorted multisegment.
     *
     * Since Segment.compareTo() orders by
     *
     *     b ascending,
     *     e descending on ties,
     *
     * and equal-depth segments are comparable by containment,
     * restricting this ordering to one depth fiber gives
     *
     *     Delta_i1 ⊇ ... ⊇ Delta_il.
     *
     * Time complexity after depths are known: O(n + d).
     */
    private List<List<Integer>> admissibleEnumerations() {

        if (admissibleEnumerations != null) {
            return admissibleEnumerations;
        }

        List<Segment> distinct = distinctSegments();
        List<Integer> cumulative = cumulativeFreq();
        int[] longest = longestStarting();

        admissibleEnumerations = new ArrayList<>();

        if (distinct.isEmpty()) {
            return admissibleEnumerations;
        }


        int maxDepth = 0;

        for (int i = 0; i < distinct.size(); i++) {
            maxDepth =
                Math.max(
                    maxDepth,
                    longest[i] - 1
                );
        }

        // creating a new list for each depth index
        for (int k = 0; k <= maxDepth; k++) {
            admissibleEnumerations.add(
                new ArrayList<>()
            );
        }

        /* 1. scan the distinct element list one-by-one,
        * 2. lookup the depth of that element
        * 3. attach it at the end of the list corresponding to that depth
        *    and attach all indicies of its copies (exploiting the cumulative frequencies list)
        */

        for (int i = 0; i < distinct.size(); i++) {

            int depth = longest[i] - 1;

            int firstOccurrence =                       // first Occurrence in the sense that it is the index of the first occurrence of that segment
                (i == 0)
                    ? 0
                    : cumulative.get(i - 1);

            int lastOccurrence =
                cumulative.get(i) - 1;


            for (
                int index = firstOccurrence;
                index <= lastOccurrence;
                index++
            ) {
                admissibleEnumerations
                    .get(depth)
                    .add(index);
            }
        }


        return admissibleEnumerations;
    }


    /*
     * Given an index in the expanded sorted multisegment,
     * returns the corresponding distinct-segment index (first occurrence).
     * this is Binary Search
     * Time complexity: O(log d).
     */
    public int distinctIndex(int index) {

        if (index < 0 || index >= ms.size()) {
            throw new IndexOutOfBoundsException();
        }

        List<Integer> cumulative = cumulativeFreq();

        int left = 0;
        int right = cumulative.size() - 1;

        while (left < right) {

            int mid = (left + right) / 2;

            if (index < cumulative.get(mid)) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }

        return left;
    }


    /*
     * Returns Delta_i.
     */
    private Segment segmentAt(int index) {

        return distinctSegments().get(
            distinctIndex(index)
        );
    }


    /*
     * Returns the length of a longest precedence chain
     * starting at Delta_i.
     */
    public int longestChainStartingAt(int index) {

        int distinct = distinctIndex(index);

        return longestStarting()[distinct];
    }


    /*
     * Returns d(i).
     */
    public int depth(int index) {

        return longestChainStartingAt(index) - 1;
    }


    /*
     * Returns Delta'_i.
     *
     * We do not explicitly construct i^vee.
     * The next index is obtained directly from the admissible
     * enumeration of the depth fiber containing i.
     */
    public Segment SegmentTransform(int i) {

        int depth = depth(i);

        List<Integer> enumeration =
            admissibleEnumerations().get(depth);

        int position =
            Collections.binarySearch(enumeration, i);

        int nextIndex =
            enumeration.get((position + 1) % enumeration.size());

        return new Segment(
            segmentAt(i).b,
            segmentAt(nextIndex).e
        );
    }


    /*
     * I' = {j_0, ..., j_d(m)}.
     *
     * j_k is the final element of the admissible
     * enumeration of d^{-1}(k).
     * using LinkedHashSet which is a Hash table and doubly-linked list 
     */
    public Set<Integer> DistinguishedIndices() {

        Set<Integer> result =
            new LinkedHashSet<>();              //could possibly use another implementation like a List (set is not necessary but better complexity-wise for lookup later)

        for (List<Integer> enumeration : admissibleEnumerations()) {
            result.add(enumeration.get(enumeration.size() - 1));
        }

        return result;
    }


    /*
     * Computes l(m).
     *
     * For a fiber
     *
     *     Delta_i1 ⊇ ... ⊇ Delta_il,
     *
     * the corresponding segment in l(m) is
     *
     *     [ b(Delta_il), e(Delta_i1) ].
     *
     */
    public MultiSegment l() {

        List<List<Integer>> enumerations =
            admissibleEnumerations();

        Segment[] segments =
            new Segment[enumerations.size()];


        for (int k = 0; k < enumerations.size(); k++) {

            List<Integer> enumeration =
                enumerations.get(k);

            Segment first =
                segmentAt(enumeration.get(0));

            Segment last =
                segmentAt(
                    enumeration.get(
                        enumeration.size() - 1
                    )
                );

            segments[k] =
                new Segment(
                    last.b,
                    first.e
                );
        }


        return new MultiSegment(segments);
    }


    /*
     * Computes m'.
     *
     * In each admissible enumeration
     *
     *     [i_1, ..., i_l],
     *
     * the final index i_l belongs to I'.
     * Thus m' contains Delta'_i for i_1, ..., i_{l-1}.
     */
    public MultiSegment DerivedMultisegment() {

        List<Segment> result = new ArrayList<>();

        for (List<Integer> enumeration : admissibleEnumerations()) {

            for (int p = 0; p < enumeration.size() - 1; p++) {

                Segment current =segmentAt(enumeration.get(p));
                Segment next = segmentAt(enumeration.get(p + 1));
                result.add(new Segment(current.b, next.e));
            }
        }

        return new MultiSegment(result.toArray(new Segment[0]));
    }



    public int size() {
        return ms.size();
    }


    //given an distinct segment index, finds its index in the multisegment
    public int firstOccurrenceIndex(int distinctIndex) {
        if (distinctIndex == 0) {
            return 0;
        }

        return cumulativeFreq().get(distinctIndex - 1);
    }

    /*
    * Constructs the sequence i_1, i_2, ... from Definition 3.1.
    *
    * We use the ordering of distinctSegments:
    *
    *     b ascending,
    *     e descending for equal b.
    *
    * Hence:
    * - for minimal b, the last segment in that b-block has minimal e;
    * - for b = previous.b + 1, we scan that block until e is no
    *   longer large enough. The last valid segment has minimal e.
    *
    */
    public List<Integer> LeadingIndices() {

        List<Segment> distinct = distinctSegments();

        List<Integer> result = new ArrayList<>();

        if (distinct.isEmpty()) {
            return result;
        }

        int n = distinct.size();

        // Find i_1:
        // minimal b, and among those, minimal e.
        int current = 0;
        int minB = distinct.get(0).b;

        while (current + 1 < n && distinct.get(current + 1).b == minB) {
            current++;
        }

        // Choose the first occurrence of this distinct segment.
        result.add(firstOccurrenceIndex(current));


        while (true) {

            Segment previous = distinct.get(current);
            int j = current + 1;

            // Skip the rest of the current b-block, if any.
            while (j < n && distinct.get(j).b == previous.b) {
                j++;
            }

            // We need b = previous.b + 1.
            if (j == n || distinct.get(j).b != previous.b + 1) {
                break;
            }

            int next = -1;
            int targetB = previous.b + 1;


            /*
            * e is descending inside this block.
            *
            * As long as previous.e < candidate.e,
            * candidate is valid.
            *
            * We keep moving forward so that next becomes
            * the valid candidate with the smallest e.
            *
            * Once candidate.e <= previous.e, we can stop:
            * all later e's are even smaller.
            */
            while (j < n && distinct.get(j).b == targetB) {

                if (previous.e < distinct.get(j).e) {
                    next = j;} 
                else {
                    break;
                }

                j++;
            }


            if (next == -1) {
                break;
            }

            current = next;

            // Again choose the first occurrence of this distinct segment.
            result.add(firstOccurrenceIndex(current));
        }


        return result;
    }

    /*
    * Computes
    *
    *     Delta°(m) = [min m, min m + k - 1],
    *
    * where k is the length of the sequence produced by LeadingIndices().
    */
    public Segment DeltaCircle() {

        if (ms.isEmpty()) {
            throw new IllegalStateException("Multisegment must be nonempty.");
        }

        int min = ms.firstEntry().getElement().b;
        int k = LeadingIndices().size();

        return new Segment(min, min + k - 1);
    }


    /*
    * Computes Delta*_i.
    */
    private Optional<Segment> deltaStar(int i) {

        Segment s = segmentAt(i);

        if (!LeadingIndices().contains(i)) {
            return Optional.of(s);
        }

        // truncateLeft[a,a] = empty
        if (s.b == s.e) {
            return Optional.empty();
        }

        return Optional.of(
            new Segment(s.b + 1, s.e)
        );
    }


    /*
    * Computes m† = sum Delta*_i,
    * discarding empty summands.
    */
    public MultiSegment MCross() {

        List<Segment> result = new ArrayList<>();

        for (int i = 0; i < ms.size(); i++) {
            deltaStar(i).ifPresent(result::add);
        }

        return new MultiSegment(
            result.toArray(new Segment[0])
        );
    }
}