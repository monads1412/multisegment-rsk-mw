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

        assertEquals(
            expectedB,
            actual.b,
            "Wrong beginning."
        );

        assertEquals(
            expectedE,
            actual.e,
            "Wrong ending."
        );
    }


    private static void assertSameSegment(
        Segment expected,
        Segment actual
    ) {
        assertNotNull(actual);

        assertEquals(
            expected.b,
            actual.b,
            "Wrong beginning."
        );

        assertEquals(
            expected.e,
            actual.e,
            "Wrong ending."
        );
    }


    /*
     * Test-only access to the expanded sorted multisegment.
     *
     * This avoids changing MultiSegment merely to make testing easier.
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
     * Canonical representation preserving repetitions.
     */
    private static List<String> signature(
        List<Segment> segments
    ) {

        List<Segment> copy =
            new ArrayList<>(segments);

        Collections.sort(copy);

        List<String> result =
            new ArrayList<>();

        for (Segment segment : copy) {
            result.add(
                "[" + segment.b + "," + segment.e + "]"
            );
        }

        return result;
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


    // ============================================================
    // Independent naïve implementations
    // ============================================================


    /*
     * Slow O(n^2) implementation of depth directly on
     * expanded occurrences.
     */
    private static int[] naiveDepths(
        List<Segment> segments
    ) {

        int n = segments.size();

        int[] longest = new int[n];

        for (int i = n - 1; i >= 0; i--) {

            longest[i] = 1;

            for (int j = i + 1; j < n; j++) {

                if (
                    segments.get(i)
                        .precedes(segments.get(j))
                ) {
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


    /*
     * Direct implementation of Definition 3.1.
     *
     * We deliberately do NOT use the optimization from
     * MultiSegment.LeadingIndices().
     */
    private static List<Integer> naiveLeadingIndices(
        List<Segment> segments
    ) {

        List<Integer> result =
            new ArrayList<>();

        if (segments.isEmpty()) {
            return result;
        }


        int minB = Integer.MAX_VALUE;

        for (Segment segment : segments) {
            minB = Math.min(minB, segment.b);
        }


        int current = -1;
        int minimumE = Integer.MAX_VALUE;

        /*
         * For ties caused by repeated equal segments,
         * choose the final occurrence. This matches the
         * canonical choice made by the implementation.
         */
        for (int i = 0; i < segments.size(); i++) {

            Segment candidate = segments.get(i);

            if (
                candidate.b == minB &&
                candidate.e <= minimumE
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


            for (
                int i = 0;
                i < segments.size();
                i++
            ) {

                Segment candidate =
                    segments.get(i);

                if (
                    candidate.b == targetB &&
                    previous.precedes(candidate) &&
                    candidate.e <= bestE
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
            maxDepth =
                Math.max(maxDepth, depth);
        }


        for (
            int k = 0;
            k <= maxDepth;
            k++
        ) {
            fibers.add(new ArrayList<>());
        }


        for (
            int i = 0;
            i < depths.length;
            i++
        ) {
            fibers.get(depths[i]).add(i);
        }


        return fibers;
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
                fiber.get(
                    fiber.size() - 1
                );


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
                    segments.get(
                        fiber.get(p)
                    );

                Segment next =
                    segments.get(
                        fiber.get(p + 1)
                    );


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


        for (
            int i = 0;
            i < segments.size();
            i++
        ) {

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

            // If b == e and i is in I*, the summand is empty.
        }


        return result;
    }


    // ============================================================
    // Segment tests
    // ============================================================


    @Test
    public void segmentOperations() {

        Segment a = s(1, 7);
        Segment b = s(2, 5);
        Segment c = s(4, 9);
        Segment invalid = s(6, 3);


        assertTrue(a.isSegment(a));
        assertTrue(s(3, 3).isSegment(s(3, 3)));

        assertFalse(
            invalid.isSegment(invalid)
        );


        assertTrue(
            b.precedes(c)
        );

        assertFalse(
            a.precedes(b)
        );

        assertFalse(
            a.precedes(a)
        );

        assertFalse(
            invalid.precedes(c)
        );


        /*
         * According to your subsetEq implementation,
         * subsetEq(outer, inner) checks inner ⊆ outer.
         */
        assertTrue(
            a.subsetEq(a, b)
        );

        assertFalse(
            a.subsetEq(b, a)
        );

        assertTrue(
            a.subsetEq(a, a)
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
            signature(segments)
        );
    }


    // ============================================================
    // Empty and minimal edge cases
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
            () -> m.SegmentTransform(0)
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

        assertEquals(
            Set.of(0),
            m.DistinguishedIndices()
        );


        assertSegment(
            5,
            5,
            m.SegmentTransform(0)
        );

        assertSegment(
            5,
            5,
            m.DeltaCircle()
        );


        assertSameMultisegment(
            List.of(s(5, 5)),
            m.l()
        );


        assertEquals(
            0,
            m.DerivedMultisegment().size()
        );


        /*
         * Delta* = -[5,5] = empty.
         */
        assertEquals(
            0,
            m.MCross().size()
        );
    }


    // ============================================================
    // Repetition edge case
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
         * The implementation chooses the final occurrence
         * of the identical segment for i1.
         */
        assertEquals(
            List.of(3),
            m.LeadingIndices()
        );


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
            List.of(
                s(2, 5),
                s(2, 5),
                s(2, 5)
            ),
            m.DerivedMultisegment()
        );


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
    // Main hard deterministic example
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
         * 0  [1,4]      depth 2
         * 1  [2,3]      depth 2
         * 2  [4,8]      depth 1
         * 3  [5,7]      depth 1
         * 4  [8,12]     depth 0
         * 5  [9,11]     depth 0
         * 6  [9,11]     depth 0
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
         * Hence
         *
         * I' = {6,3,1}.
         */
        assertEquals(
            Set.of(1, 3, 6),
            m.DistinguishedIndices()
        );


        assertSegment(
            1,
            3,
            m.SegmentTransform(0)
        );

        assertSegment(
            2,
            4,
            m.SegmentTransform(1)
        );

        assertSegment(
            4,
            7,
            m.SegmentTransform(2)
        );

        assertSegment(
            5,
            8,
            m.SegmentTransform(3)
        );

        assertSegment(
            8,
            11,
            m.SegmentTransform(4)
        );

        assertSegment(
            9,
            11,
            m.SegmentTransform(5)
        );

        assertSegment(
            9,
            12,
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
    // Hard test specifically for Definition 3.1
    // ============================================================


    @Test
    public void leadingIndicesChoosesMinimalEAndStopsCorrectly() {

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
         *  4 [1,3]
         *  5 [1,3]    <- i2
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
         * At [3,5], b+1 exists, but [4,5] does NOT
         * strictly follow it because 5 < 5 is false.
         */


        assertEquals(
            List.of(1, 5, 7, 10),
            m.LeadingIndices()
        );


        /*
         * min m = 0, k = 4
         *
         * Delta°(m) = [0,3].
         */
        assertSegment(
            0,
            3,
            m.DeltaCircle()
        );
    }


    // ============================================================
    // Randomized test against independent naïve algorithms
    // ============================================================


    @Test
    public void randomizedAgainstNaiveDefinitions() {

        Random random =
            new Random(0x5EEDBEEFL);


        for (
            int trial = 0;
            trial < 300;
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

            List<Segment> canonical =
                expanded(m);

            int[] naiveDepth =
                naiveDepths(canonical);


            String message =
                "Trial " + trial
                + ", m = "
                + signature(canonical);


            // -------------------------
            // depth
            // -------------------------

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


            // -------------------------
            // SegmentTransform
            // -------------------------

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


            // -------------------------
            // I'
            // -------------------------

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


            // -------------------------
            // l(m)
            // -------------------------

            assertSameMultisegment(
                naiveL(
                    canonical,
                    naiveDepth
                ),
                m.l()
            );


            // -------------------------
            // m'
            // -------------------------

            assertSameMultisegment(
                naiveDerived(
                    canonical,
                    naiveDepth
                ),
                m.DerivedMultisegment()
            );


            // -------------------------
            // i1,...,ik
            // -------------------------

            List<Integer> expectedLeading =
                naiveLeadingIndices(canonical);

            assertEquals(
                expectedLeading,
                m.LeadingIndices(),
                message
                + ", wrong LeadingIndices"
            );


            // -------------------------
            // Delta°
            // -------------------------

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


            // -------------------------
            // m†
            // -------------------------

            assertSameMultisegment(
                naiveMCross(canonical),
                m.MCross()
            );
        }
    }


    // ============================================================
    // Corollary
    //
    //     l(m) = l(m†)
    //     Delta°(m) = Delta°(m†)
    //     (m†)' = (m')†
    //
    // ============================================================


    private static void assertCorollary(
        MultiSegment m
    ) {

        assertTrue(
            m.size() > 0,
            "The corollary is being tested only for nonzero m."
        );


        MultiSegment mCross =
            m.MCross();


        // l(m) = l(m†)
        assertSameMultisegment(
            m.l(),
            mCross.l()
        );


        /*
         * DeltaCircle is currently defined only for a
         * nonempty multisegment.
         */
        if (mCross.size() > 0) {

            assertSameSegment(
                m.DeltaCircle(),
                mCross.DeltaCircle()
            );
        }


        // (m†)' = (m')†
        assertSameMultisegment(
            mCross.DerivedMultisegment(),
            m.DerivedMultisegment()
                .MCross()
        );
    }

}