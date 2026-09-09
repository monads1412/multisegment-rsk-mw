package com.salma;

import static org.junit.jupiter.api.Assertions.*;

import java.lang.reflect.Field;
import java.util.*;

import org.junit.jupiter.api.Test;

import com.google.common.collect.SortedMultiset;


public class MultiSegmentTest {


    // ============================================================
    // Helpers
    // ============================================================


    private static Segment s(int b, int e) {
        return new Segment(b, e);
    }


    private static void assertSegment(
        int expectedB,
        int expectedE,
        Segment actual
    ) {
        assertNotNull(actual);
        assertEquals(expectedB, actual.b, "Wrong beginning.");
        assertEquals(expectedE, actual.e, "Wrong ending.");
    }


    private static void assertSameSegment(
        Segment expected,
        Segment actual
    ) {
        assertSegment(expected.b, expected.e, actual);
    }


    /*
     * Test-only access to the expanded sorted multisegment.
     */
    @SuppressWarnings("unchecked")
    private static List<Segment> expanded(MultiSegment m) {

        try {
            Field field =
                MultiSegment.class.getDeclaredField("ms");

            field.setAccessible(true);

            SortedMultiset<Segment> ms =
                (SortedMultiset<Segment>) field.get(m);

            return new ArrayList<>(ms);

        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }


    /*
     * Converts segments to strings without changing their order.
     */
    private static List<String> orderedSignature(
        List<Segment> segments
    ) {
        List<String> result = new ArrayList<>();

        for (Segment segment : segments) {
            result.add(
                "[" + segment.b + "," + segment.e + "]"
            );
        }

        return result;
    }


    /*
     * Canonical representation of a multisegment.
     * Repetitions are preserved.
     */
    private static List<String> signature(
        List<Segment> segments
    ) {
        List<Segment> copy =
            new ArrayList<>(segments);

        Collections.sort(copy);

        return orderedSignature(copy);
    }


    private static List<String> signature(
        MultiSegment m
    ) {
        return signature(expanded(m));
    }


    private static void assertSameMultisegment(
        List<Segment> expected,
        MultiSegment actual
    ) {
        assertEquals(
            signature(expected),
            signature(actual)
        );
    }


    private static void assertSameMultisegment(
        MultiSegment expected,
        MultiSegment actual
    ) {
        assertEquals(
            signature(expected),
            signature(actual)
        );
    }


    private static int minB(
        List<Segment> segments
    ) {
        if (segments.isEmpty()) {
            throw new IllegalArgumentException(
                "Multisegment must be nonempty."
            );
        }

        int min = Integer.MAX_VALUE;

        for (Segment segment : segments) {
            min = Math.min(min, segment.b);
        }

        return min;
    }


    // ============================================================
    // Independent naïve implementations
    // ============================================================


    /*
     * Direct O(n^2) implementation of depth on the
     * expanded multisegment.
     */
    private static int[] naiveDepths(
        List<Segment> segments
    ) {
        int n = segments.size();
        int[] longest = new int[n];

        for (int i = n - 1; i >= 0; i--) {

            longest[i] = 1;

            for (int j = i + 1; j < n; j++) {

                if (segments.get(i).precedes(segments.get(j))) {
                    longest[i] =
                        Math.max(
                            longest[i],
                            1 + longest[j]
                        );
                }
            }
        }

        int[] depth = new int[n];

        for (int i = 0; i < n; i++) {
            depth[i] = longest[i] - 1;
        }

        return depth;
    }


    private static List<List<Integer>> naiveFibers(
        int[] depths
    ) {
        List<List<Integer>> fibers =
            new ArrayList<>();

        if (depths.length == 0) {
            return fibers;
        }

        int maxDepth = 0;

        for (int depth : depths) {
            maxDepth = Math.max(maxDepth, depth);
        }

        for (int k = 0; k <= maxDepth; k++) {
            fibers.add(new ArrayList<>());
        }

        for (int i = 0; i < depths.length; i++) {
            fibers.get(depths[i]).add(i);
        }

        return fibers;
    }


    /*
     * Direct implementation of Definition 3.1.
     *
     * IMPORTANT:
     * if several equal copies are possible, this chooses
     * the FIRST occurrence, matching our canonical convention.
     */
    private static List<Integer> naiveLeadingIndices(
        List<Segment> segments
    ) {
        List<Integer> result =
            new ArrayList<>();

        if (segments.isEmpty()) {
            return result;
        }


        // Find min m.
        int minB = Integer.MAX_VALUE;

        for (Segment segment : segments) {
            minB = Math.min(minB, segment.b);
        }


        // Find i1:
        // b minimal, then e minimal.
        // Strict < means an equal later copy does not replace
        // the first occurrence.
        int current = -1;
        int minimumE = Integer.MAX_VALUE;

        for (int i = 0; i < segments.size(); i++) {

            Segment candidate =
                segments.get(i);

            if (
                candidate.b == minB &&
                candidate.e < minimumE
            ) {
                minimumE = candidate.e;
                current = i;
            }
        }

        result.add(current);


        while (true) {

            Segment previous =
                segments.get(current);

            int targetB =
                previous.b + 1;

            int next = -1;
            int bestE = Integer.MAX_VALUE;


            /*
             * Search directly through all occurrences.
             *
             * Again, strict < ensures that if the best segment
             * has repeated equal copies, the first one is kept.
             */
            for (int i = 0; i < segments.size(); i++) {

                Segment candidate =
                    segments.get(i);

                if (
                    candidate.b == targetB &&
                    previous.precedes(candidate) &&
                    candidate.e < bestE
                ) {
                    bestE = candidate.e;
                    next = i;
                }
            }


            if (next == -1) {
                break;
            }

            result.add(next);
            current = next;
        }

        return result;
    }


    private static Segment naiveSegmentTransform(
        List<Segment> segments,
        int[] depths,
        int index
    ) {
        List<List<Integer>> fibers =
            naiveFibers(depths);

        List<Integer> fiber =
            fibers.get(depths[index]);

        int position =
            fiber.indexOf(index);

        int next =
            fiber.get(
                (position + 1) % fiber.size()
            );

        return new Segment(
            segments.get(index).b,
            segments.get(next).e
        );
    }


    private static List<Segment> naiveL(
        List<Segment> segments,
        int[] depths
    ) {
        List<Segment> result =
            new ArrayList<>();

        for (
            List<Integer> fiber :
            naiveFibers(depths)
        ) {
            int first = fiber.get(0);
            int last =
                fiber.get(fiber.size() - 1);

            result.add(
                new Segment(
                    segments.get(last).b,
                    segments.get(first).e
                )
            );
        }

        return result;
    }


    private static List<Segment> naiveDerived(
        List<Segment> segments,
        int[] depths
    ) {
        List<Segment> result =
            new ArrayList<>();

        for (
            List<Integer> fiber :
            naiveFibers(depths)
        ) {
            for (
                int p = 0;
                p < fiber.size() - 1;
                p++
            ) {
                Segment current =
                    segments.get(fiber.get(p));

                Segment next =
                    segments.get(fiber.get(p + 1));

                result.add(
                    new Segment(
                        current.b,
                        next.e
                    )
                );
            }
        }

        return result;
    }


    private static List<Segment> naiveMCross(
        List<Segment> segments
    ) {
        Set<Integer> IStar =
            new HashSet<>(
                naiveLeadingIndices(segments)
            );

        List<Segment> result =
            new ArrayList<>();

        for (int i = 0; i < segments.size(); i++) {

            Segment segment =
                segments.get(i);

            if (!IStar.contains(i)) {
                result.add(segment);

            } else if (segment.b < segment.e) {

                result.add(
                    new Segment(
                        segment.b + 1,
                        segment.e
                    )
                );
            }

            // If [a,a] is leading, truncation is empty,
            // so nothing is added.
        }

        return result;
    }


    // ============================================================
    // Segment tests
    // ============================================================


    @Test
    public void segmentOperations() {

        Segment outer = s(1, 7);
        Segment inner = s(2, 5);
        Segment later = s(4, 9);
        Segment point = s(3, 3);
        Segment invalid = s(6, 3);

        assertTrue(outer.isSegment(outer));
        assertTrue(point.isSegment(point));
        assertFalse(invalid.isSegment(invalid));

        assertTrue(inner.precedes(later));

        assertFalse(outer.precedes(inner));
        assertFalse(outer.precedes(outer));
        assertFalse(invalid.precedes(later));

        // subsetEq(s1,s2) means s2 ⊆ s1.
        assertTrue(
            outer.subsetEq(outer, inner)
        );

        assertFalse(
            outer.subsetEq(inner, outer)
        );

        assertTrue(
            outer.subsetEq(outer, outer)
        );
    }


    @Test
    public void segmentOrderingIsBAscendingThenEDescending() {

        List<Segment> segments =
            new ArrayList<>(
                Arrays.asList(
                    s(2, 3),
                    s(1, 4),
                    s(1, 7),
                    s(2, 10),
                    s(1, 5)
                )
            );

        Collections.sort(segments);

        assertEquals(
            Arrays.asList(
                "[1,7]",
                "[1,5]",
                "[1,4]",
                "[2,10]",
                "[2,3]"
            ),
            orderedSignature(segments)
        );
    }


    // ============================================================
    // Empty and singleton cases
    // ============================================================


    @Test
    public void emptyMultisegment() {

        MultiSegment m =
            new MultiSegment();

        assertEquals(0, m.size());

        assertTrue(
            m.LeadingIndices().isEmpty()
        );

        assertTrue(
            m.DistinguishedIndices().isEmpty()
        );

        assertEquals(
            0,
            m.l().size()
        );

        assertEquals(
            0,
            m.DerivedMultisegment().size()
        );

        assertEquals(
            0,
            m.MCross().size()
        );

        assertThrows(
            IllegalStateException.class,
            m::DeltaCircle
        );

        assertThrows(
            IndexOutOfBoundsException.class,
            () -> m.distinctIndex(0)
        );

        assertThrows(
            IndexOutOfBoundsException.class,
            () -> m.distinctIndex(-1)
        );

        assertThrows(
            IndexOutOfBoundsException.class,
            () -> m.SegmentTransform(0)
        );
    }


    @Test
    public void singletonNonPointSegment() {

        MultiSegment m =
            new MultiSegment(
                s(5, 8)
            );

        assertEquals(1, m.size());
        assertEquals(0, m.depth(0));

        assertEquals(
            List.of(0),
            m.LeadingIndices()
        );

        assertEquals(
            Set.of(0),
            m.DistinguishedIndices()
        );

        assertSegment(
            5,
            8,
            m.SegmentTransform(0)
        );

        assertSegment(
            5,
            5,
            m.DeltaCircle()
        );

        assertSameMultisegment(
            List.of(s(5, 8)),
            m.l()
        );

        assertEquals(
            0,
            m.DerivedMultisegment().size()
        );

        // -[5,8] = [6,8].
        assertSameMultisegment(
            List.of(s(6, 8)),
            m.MCross()
        );
    }


    @Test
    public void singletonPointSegment() {

        MultiSegment m =
            new MultiSegment(
                s(5, 5)
            );

        assertEquals(1, m.size());
        assertEquals(0, m.depth(0));

        assertEquals(
            List.of(0),
            m.LeadingIndices()
        );

        assertSegment(
            5,
            5,
            m.DeltaCircle()
        );

        // -[5,5] = empty.
        assertEquals(
            0,
            m.MCross().size()
        );
    }


    // ============================================================
    // Expanded/distinct index tests
    // ============================================================


    @Test
    public void distinctIndexHandlesMultiplicities() {

        MultiSegment m =
            new MultiSegment(
                s(3, 4),

                s(1, 8),
                s(1, 8),

                s(1, 5),
                s(1, 5),
                s(1, 5),

                s(2, 7)
            );

        /*
         * Expanded order:
         *
         * 0 [1,8]   distinct 0
         * 1 [1,8]   distinct 0
         *
         * 2 [1,5]   distinct 1
         * 3 [1,5]   distinct 1
         * 4 [1,5]   distinct 1
         *
         * 5 [2,7]   distinct 2
         *
         * 6 [3,4]   distinct 3
         */

        assertEquals(0, m.distinctIndex(0));
        assertEquals(0, m.distinctIndex(1));

        assertEquals(1, m.distinctIndex(2));
        assertEquals(1, m.distinctIndex(3));
        assertEquals(1, m.distinctIndex(4));

        assertEquals(2, m.distinctIndex(5));
        assertEquals(3, m.distinctIndex(6));

        assertThrows(
            IndexOutOfBoundsException.class,
            () -> m.distinctIndex(-1)
        );

        assertThrows(
            IndexOutOfBoundsException.class,
            () -> m.distinctIndex(7)
        );
    }


    // ============================================================
    // Repeated equal segments
    // ============================================================


    @Test
    public void fourIdenticalSegments() {

        MultiSegment m =
            new MultiSegment(
                s(2, 5),
                s(2, 5),
                s(2, 5),
                s(2, 5)
            );

        assertEquals(4, m.size());

        for (int i = 0; i < 4; i++) {

            assertEquals(
                0,
                m.depth(i)
            );

            assertSegment(
                2,
                5,
                m.SegmentTransform(i)
            );
        }


        /*
         * LeadingIndices uses our canonical convention:
         * choose the FIRST equal occurrence.
         */
        assertEquals(
            List.of(0),
            m.LeadingIndices()
        );


        /*
         * This is different from I'.
         *
         * j_0 is the LAST element of the admissible
         * depth-0 enumeration.
         */
        assertEquals(
            Set.of(3),
            m.DistinguishedIndices()
        );


        assertSegment(
            2,
            2,
            m.DeltaCircle()
        );


        assertSameMultisegment(
            List.of(
                s(2, 5)
            ),
            m.l()
        );


        assertSameMultisegment(
            Arrays.asList(
                s(2, 5),
                s(2, 5),
                s(2, 5)
            ),
            m.DerivedMultisegment()
        );


        /*
         * The first copy is truncated:
         *
         * [2,5] -> [3,5].
         *
         * The other three copies remain.
         */
        assertSameMultisegment(
            Arrays.asList(
                s(2, 5),
                s(2, 5),
                s(2, 5),
                s(3, 5)
            ),
            m.MCross()
        );
    }


    // ============================================================
    // Depth tests
    // ============================================================


    @Test
    public void completeChainHasAllDepths() {

        MultiSegment m =
            new MultiSegment(
                s(0, 2),
                s(1, 3),
                s(2, 4),
                s(3, 5)
            );

        assertEquals(3, m.depth(0));
        assertEquals(2, m.depth(1));
        assertEquals(1, m.depth(2));
        assertEquals(0, m.depth(3));

        /*
         * This also explicitly checks that if maxDepth = 3,
         * all depths 0,1,2,3 occur.
         */
        Set<Integer> depths =
            new HashSet<>();

        for (int i = 0; i < m.size(); i++) {
            depths.add(m.depth(i));
        }

        assertEquals(
            Set.of(0, 1, 2, 3),
            depths
        );
    }


    // ============================================================
    // Main deterministic RSK example
    // ============================================================


    @Test
    public void hardDepthAndKConstructionExample() {

        MultiSegment m =
            new MultiSegment(
                s(9, 11),
                s(1, 4),
                s(5, 7),
                s(8, 12),
                s(2, 3),
                s(9, 11),
                s(4, 8)
            );


        /*
         * Expanded canonical order:
         *
         * 0 [1,4]    depth 2
         * 1 [2,3]    depth 2
         * 2 [4,8]    depth 1
         * 3 [5,7]    depth 1
         * 4 [8,12]   depth 0
         * 5 [9,11]   depth 0
         * 6 [9,11]   depth 0
         */

        int[] expectedDepths =
            {2, 2, 1, 1, 0, 0, 0};

        for (
            int i = 0;
            i < expectedDepths.length;
            i++
        ) {
            assertEquals(
                expectedDepths[i],
                m.depth(i),
                "Wrong depth at index " + i
            );
        }


        /*
         * Fibers:
         *
         * d^-1(0) = [4,5,6]
         * d^-1(1) = [2,3]
         * d^-1(2) = [0,1]
         *
         * Therefore I' = {6,3,1}.
         */
        assertEquals(
            Set.of(1, 3, 6),
            m.DistinguishedIndices()
        );


        assertSegment(
            1, 3,
            m.SegmentTransform(0)
        );

        assertSegment(
            2, 4,
            m.SegmentTransform(1)
        );

        assertSegment(
            4, 7,
            m.SegmentTransform(2)
        );

        assertSegment(
            5, 8,
            m.SegmentTransform(3)
        );

        assertSegment(
            8, 11,
            m.SegmentTransform(4)
        );

        assertSegment(
            9, 11,
            m.SegmentTransform(5)
        );

        assertSegment(
            9, 12,
            m.SegmentTransform(6)
        );


        assertSameMultisegment(
            Arrays.asList(
                s(2, 4),
                s(5, 8),
                s(9, 12)
            ),
            m.l()
        );


        assertSameMultisegment(
            Arrays.asList(
                s(1, 3),
                s(4, 7),
                s(8, 11),
                s(9, 11)
            ),
            m.DerivedMultisegment()
        );


        assertEquals(
            List.of(0),
            m.LeadingIndices()
        );


        assertSegment(
            1,
            1,
            m.DeltaCircle()
        );


        assertSameMultisegment(
            Arrays.asList(
                s(2, 4),
                s(2, 3),
                s(4, 8),
                s(5, 7),
                s(8, 12),
                s(9, 11),
                s(9, 11)
            ),
            m.MCross()
        );
    }


    // ============================================================
    // Leading indices
    // ============================================================


    @Test
    public void leadingIndicesChoosesMinimalEAndFirstEqualCopy() {

        MultiSegment m =
            new MultiSegment(
                s(3, 5),
                s(1, 3),
                s(0, 2),
                s(2, 3),
                s(1, 9),
                s(4, 5),
                s(0, 8),
                s(2, 4),
                s(3, 7),
                s(2, 10),
                s(1, 5),
                s(1, 3)
            );


        /*
         * Expanded order:
         *
         *  0 [0,8]
         *  1 [0,2]    <- i1
         *
         *  2 [1,9]
         *  3 [1,5]
         *  4 [1,3]    <- i2: FIRST equal copy
         *  5 [1,3]
         *
         *  6 [2,10]
         *  7 [2,4]    <- i3
         *  8 [2,3]
         *
         *  9 [3,7]
         * 10 [3,5]    <- i4
         *
         * 11 [4,5]
         *
         * [4,5] cannot follow [3,5],
         * because the ending inequality is strict.
         */

        assertEquals(
            List.of(1, 4, 7, 10),
            m.LeadingIndices()
        );


        /*
         * min m = 0 and k = 4.
         *
         * Delta°(m) = [0,3].
         */
        assertSegment(
            0,
            3,
            m.DeltaCircle()
        );
    }


    @Test
    public void leadingIndicesStopsWhenNextBeginningIsMissing() {

        MultiSegment m =
            new MultiSegment(
                s(0, 2),
                s(2, 100),
                s(3, 101)
            );

        /*
         * i1 = [0,2].
         *
         * Definition 3.1 requires the next beginning
         * to be exactly 1.
         *
         * No such segment exists, so we stop immediately.
         */
        assertEquals(
            List.of(0),
            m.LeadingIndices()
        );

        assertSegment(
            0,
            0,
            m.DeltaCircle()
        );
    }


    @Test
    public void leadingIndicesStopsWhenNextBlockHasNoValidEnding() {

        MultiSegment m =
            new MultiSegment(
                s(0, 5),
                s(1, 5),
                s(1, 4),
                s(2, 100)
            );

        /*
         * i1 = [0,5].
         *
         * At b = 1 we have [1,5], [1,4],
         * but neither satisfies 5 < e.
         *
         * We therefore stop, even though later b-blocks exist.
         */
        assertEquals(
            List.of(0),
            m.LeadingIndices()
        );
    }


    // ============================================================
    // Randomized comparison against independent definitions
    // ============================================================


    @Test
    public void randomizedAgainstNaiveDefinitions() {

        Random random =
            new Random(0x5EEDBEEFL);


        for (
            int trial = 0;
            trial < 500;
            trial++
        ) {
            int n =
                1 + random.nextInt(12);

            Segment[] input =
                new Segment[n];


            for (int i = 0; i < n; i++) {

                int b =
                    random.nextInt(11) - 5;

                int e =
                    b + random.nextInt(7);

                input[i] =
                    new Segment(b, e);
            }


            MultiSegment m =
                new MultiSegment(input);

            List<Segment> canonical =
                expanded(m);

            int[] naiveDepth =
                naiveDepths(canonical);

            String message =
                "Trial " + trial
                + ", m = "
                + signature(canonical);


            // ------------------------------------------------
            // depth
            // ------------------------------------------------

            for (
                int i = 0;
                i < canonical.size();
                i++
            ) {
                assertEquals(
                    naiveDepth[i],
                    m.depth(i),
                    message
                    + ", wrong depth at index "
                    + i
                );
            }


            // ------------------------------------------------
            // No depth between 0 and maxDepth may be absent.
            // ------------------------------------------------

            int maxDepth = 0;

            Set<Integer> actualDepths =
                new HashSet<>();

            for (int depth : naiveDepth) {
                maxDepth =
                    Math.max(maxDepth, depth);

                actualDepths.add(depth);
            }

            for (int k = 0; k <= maxDepth; k++) {
                assertTrue(
                    actualDepths.contains(k),
                    message
                    + ", missing depth "
                    + k
                );
            }


            // ------------------------------------------------
            // Delta'_i
            // ------------------------------------------------

            for (
                int i = 0;
                i < canonical.size();
                i++
            ) {
                Segment expected =
                    naiveSegmentTransform(
                        canonical,
                        naiveDepth,
                        i
                    );

                Segment actual =
                    m.SegmentTransform(i);

                assertEquals(
                    expected.b,
                    actual.b,
                    message
                    + ", wrong Delta' beginning at "
                    + i
                );

                assertEquals(
                    expected.e,
                    actual.e,
                    message
                    + ", wrong Delta' ending at "
                    + i
                );
            }


            // ------------------------------------------------
            // I'
            // ------------------------------------------------

            Set<Integer> expectedDistinguished =
                new HashSet<>();

            for (
                List<Integer> fiber :
                naiveFibers(naiveDepth)
            ) {
                expectedDistinguished.add(
                    fiber.get(
                        fiber.size() - 1
                    )
                );
            }

            assertEquals(
                expectedDistinguished,
                m.DistinguishedIndices(),
                message + ", wrong I'"
            );


            // ------------------------------------------------
            // l(m)
            // ------------------------------------------------

            assertEquals(
                signature(
                    naiveL(
                        canonical,
                        naiveDepth
                    )
                ),
                signature(m.l()),
                message + ", wrong l(m)"
            );


            // ------------------------------------------------
            // m'
            // ------------------------------------------------

            assertEquals(
                signature(
                    naiveDerived(
                        canonical,
                        naiveDepth
                    )
                ),
                signature(
                    m.DerivedMultisegment()
                ),
                message + ", wrong m'"
            );


            // ------------------------------------------------
            // Leading indices
            // ------------------------------------------------

            List<Integer> expectedLeading =
                naiveLeadingIndices(canonical);

            assertEquals(
                expectedLeading,
                m.LeadingIndices(),
                message
                + ", wrong LeadingIndices"
            );


            // ------------------------------------------------
            // Delta°
            // ------------------------------------------------

            int min =
                canonical.get(0).b;

            int k =
                expectedLeading.size();

            Segment deltaCircle =
                m.DeltaCircle();

            assertEquals(
                min,
                deltaCircle.b,
                message
                + ", wrong DeltaCircle beginning"
            );

            assertEquals(
                min + k - 1,
                deltaCircle.e,
                message
                + ", wrong DeltaCircle ending"
            );


            // ------------------------------------------------
            // m†
            // ------------------------------------------------

            assertEquals(
                signature(
                    naiveMCross(canonical)
                ),
                signature(m.MCross()),
                message + ", wrong m†"
            );
        }
    }


    // ============================================================
    // Corollary 3.4
    //
    // Hypothesis:
    //
    //     min m < min l(m)
    //
    // Conclusions:
    //
    //     l(m) = l(m†)
    //
    //     Delta°(m) = Delta°(m')
    //
    //     (m†)' = (m')†
    // ============================================================


    private static boolean satisfiesCorollaryHypothesis(
        MultiSegment m
    ) {
        if (m.size() == 0) {
            return false;
        }

        List<Segment> original =
            expanded(m);

        List<Segment> highestLadder =
            expanded(m.l());

        return minB(original) <
               minB(highestLadder);
    }


    private static void assertCorollary(
        MultiSegment m,
        String message
    ) {
        assertTrue(
            satisfiesCorollaryHypothesis(m),
            message
            + ": hypothesis min m < min l(m) is false."
        );


        MultiSegment mDagger =
            m.MCross();

        MultiSegment mPrime =
            m.DerivedMultisegment();


        /*
         * Under the hypothesis, both are nonzero.
         */
        assertTrue(
            mDagger.size() > 0,
            message + ": m† unexpectedly empty."
        );

        assertTrue(
            mPrime.size() > 0,
            message + ": m' unexpectedly empty."
        );


        // ------------------------------------------------
        // l(m) = l(m†)
        // ------------------------------------------------

        assertEquals(
            signature(m.l()),
            signature(mDagger.l()),
            message
            + ": l(m) != l(m†)"
        );


        // ------------------------------------------------
        // Delta°(m) = Delta°(m')
        // ------------------------------------------------

        Segment leftCircle =
            m.DeltaCircle();

        Segment rightCircle =
            mPrime.DeltaCircle();

        assertEquals(
            leftCircle.b,
            rightCircle.b,
            message
            + ": Delta° beginnings differ."
        );

        assertEquals(
            leftCircle.e,
            rightCircle.e,
            message
            + ": Delta° endings differ."
        );


        // ------------------------------------------------
        // (m†)' = (m')†
        // ------------------------------------------------

        assertEquals(
            signature(
                mDagger.DerivedMultisegment()
            ),
            signature(
                mPrime.MCross()
            ),
            message
            + ": (m†)' != (m')†"
        );
    }


    @Test
    public void corollaryHardExample() {

        MultiSegment m =
            new MultiSegment(
                s(9, 11),
                s(1, 4),
                s(5, 7),
                s(8, 12),
                s(2, 3),
                s(9, 11),
                s(4, 8)
            );

        /*
         * Here
         *
         * min m = 1
         *
         * l(m) =
         * [2,4] + [5,8] + [9,12]
         *
         * so min l(m) = 2.
         *
         * Hence 1 < 2 and the corollary applies.
         */
        assertCorollary(
            m,
            "Hard deterministic corollary example"
        );
    }


    @Test
    public void corollaryWithRepeatedSegments() {

        MultiSegment m =
            new MultiSegment(
                s(1, 4),
                s(1, 4),
                s(1, 4),
                s(2, 4),
                s(3, 6),
                s(3, 5)
            );

        assertTrue(
            satisfiesCorollaryHypothesis(m)
        );

        assertCorollary(
            m,
            "Repeated-segment corollary example"
        );
    }


    @Test
    public void randomizedCorollaryUnderItsHypothesis() {

        Random random =
            new Random(0xC0110A7L);

        int tested = 0;


        for (
            int trial = 0;
            trial < 1000;
            trial++
        ) {
            int n =
                1 + random.nextInt(10);

            Segment[] input =
                new Segment[n];


            for (int i = 0; i < n; i++) {

                int b =
                    random.nextInt(9) - 3;

                int e =
                    b + random.nextInt(6);

                input[i] =
                    new Segment(b, e);
            }


            MultiSegment m =
                new MultiSegment(input);


            /*
             * Corollary 3.4 does not claim anything
             * when the hypothesis is false.
             */
            if (
                !satisfiesCorollaryHypothesis(m)
            ) {
                continue;
            }


            tested++;

            assertCorollary(
                m,
                "Corollary trial "
                + trial
                + ", m = "
                + signature(m)
            );
        }


        /*
         * Ensure that the random test did not accidentally
         * filter out almost every example.
         */
        assertTrue(
            tested >= 50,
            "Too few random multisegments satisfied "
            + "the corollary hypothesis. Tested only "
            + tested
            + "."
        );
    }
}