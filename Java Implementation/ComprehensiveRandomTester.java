package com.salma;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.*;

/**
 * Comprehensive differential/property tester for Segment + MultiSegment.
 *
 * It does NOT reuse the implementation logic as its oracle.  It reconstructs the
 * mathematical objects independently from the constructor input, then compares
 * the Java implementation against those independently computed results.
 *
 * The first argument can be either a positive sample count (random mode) or
 * "all" (exhaustive mode).  Exhaustive mode checks every nonempty multisegment
 * satisfying the supplied bounds.
 *
 * Usage:
 *   java ... com.salma.ComprehensiveRandomTester \
 *        SAMPLES|all ENDPOINT_BOUND MAX_DISTINCT MAX_MULTIPLICITY MAX_TOTAL_CARDINALITY SEED
 *
 * Examples:
 *   10000 20 4 2 5 12345
 *   all 2 3 2 4 12345
 */
public final class ComprehensiveRandomTester {

    private static long checks = 0;
    private static long corollaryCases = 0;

    private static Method distinctSegmentsMethod;
    private static Method cumulativeFreqMethod;
    private static Method longestStartingMethod;
    private static Method admissibleEnumerationsMethod;
    private static Method segmentAtMethod;
    private static Method deltaStarMethod;

    static {
        try {
            distinctSegmentsMethod = MultiSegment.class.getDeclaredMethod("distinctSegments");
            cumulativeFreqMethod = MultiSegment.class.getDeclaredMethod("cumulativeFreq");
            longestStartingMethod = MultiSegment.class.getDeclaredMethod("longestStarting");
            admissibleEnumerationsMethod = MultiSegment.class.getDeclaredMethod("admissibleEnumerations");
            segmentAtMethod = MultiSegment.class.getDeclaredMethod("segmentAt", int.class);
            deltaStarMethod = MultiSegment.class.getDeclaredMethod("deltaStar", int.class);

            distinctSegmentsMethod.setAccessible(true);
            cumulativeFreqMethod.setAccessible(true);
            longestStartingMethod.setAccessible(true);
            admissibleEnumerationsMethod.setAccessible(true);
            segmentAtMethod.setAccessible(true);
            deltaStarMethod.setAccessible(true);
        } catch (ReflectiveOperationException ex) {
            throw new ExceptionInInitializerError(ex);
        }
    }

    private ComprehensiveRandomTester() {}

    private static final class V implements Comparable<V> {
        final int b;
        final int e;

        V(int b, int e) {
            this.b = b;
            this.e = e;
        }

        @Override
        public int compareTo(V other) {
            if (b != other.b) {
                return Integer.compare(b, other.b);
            }
            return Integer.compare(other.e, e);
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof V)) {
                return false;
            }
            V other = (V) obj;
            return b == other.b && e == other.e;
        }

        @Override
        public int hashCode() {
            return 31 * b + e;
        }

        @Override
        public String toString() {
            return "[" + b + "," + e + "]";
        }
    }

    private static final class GeneratedCase {
        final Segment[] constructorInput;
        final String key;

        GeneratedCase(Segment[] constructorInput, String key) {
            this.constructorInput = constructorInput;
            this.key = key;
        }
    }

    /**
     * Independent mathematical oracle for one nonempty multisegment.
     * Global indices are 0-based to match the Java implementation.
     */
    private static final class Oracle {
        final List<V> expanded;
        final List<V> distinct;
        final List<Integer> cumulative;
        final int[] distinctIndexOfExpanded;
        final int[] firstOccurrence;
        final int[] longestDistinct;
        final int[] depth;
        final List<List<Integer>> fibers;
        final Set<Integer> distinguished;
        final List<Integer> leading;

        Oracle(Segment[] rawInput) {
            expanded = new ArrayList<>();
            for (Segment s : rawInput) {
                expanded.add(v(s));
            }
            Collections.sort(expanded);

            distinct = new ArrayList<>();
            cumulative = new ArrayList<>();
            List<Integer> firsts = new ArrayList<>();
            distinctIndexOfExpanded = new int[expanded.size()];

            int running = 0;
            int i = 0;
            while (i < expanded.size()) {
                V current = expanded.get(i);
                int dIndex = distinct.size();
                distinct.add(current);
                firsts.add(i);

                int j = i;
                while (j < expanded.size() && expanded.get(j).equals(current)) {
                    distinctIndexOfExpanded[j] = dIndex;
                    j++;
                }

                running += (j - i);
                cumulative.add(running);
                i = j;
            }

            firstOccurrence = new int[firsts.size()];
            for (i = 0; i < firsts.size(); i++) {
                firstOccurrence[i] = firsts.get(i);
            }

            // Independent O(d^2) longest-chain DP over distinct values.
            longestDistinct = new int[distinct.size()];
            for (i = distinct.size() - 1; i >= 0; i--) {
                longestDistinct[i] = 1;
                for (int j = i + 1; j < distinct.size(); j++) {
                    if (precedes(distinct.get(i), distinct.get(j))) {
                        longestDistinct[i] =
                            Math.max(longestDistinct[i], 1 + longestDistinct[j]);
                    }
                }
            }

            // Independently compute depth for every expanded global index.
            // This is intentionally done over occurrences, not by calling the
            // distinct-level optimization above.
            int n = expanded.size();
            int[] longestExpanded = new int[n];
            for (i = n - 1; i >= 0; i--) {
                longestExpanded[i] = 1;
                for (int j = i + 1; j < n; j++) {
                    if (precedes(expanded.get(i), expanded.get(j))) {
                        longestExpanded[i] =
                            Math.max(longestExpanded[i], 1 + longestExpanded[j]);
                    }
                }
            }

            depth = new int[n];
            int maxDepth = 0;
            for (i = 0; i < n; i++) {
                depth[i] = longestExpanded[i] - 1;
                maxDepth = Math.max(maxDepth, depth[i]);
            }

            fibers = new ArrayList<>();
            for (int k = 0; k <= maxDepth; k++) {
                fibers.add(new ArrayList<Integer>());
            }
            for (i = 0; i < n; i++) {
                fibers.get(depth[i]).add(i);
            }

            distinguished = new LinkedHashSet<>();
            for (List<Integer> fiber : fibers) {
                if (!fiber.isEmpty()) {
                    distinguished.add(fiber.get(fiber.size() - 1));
                }
            }

            leading = computeLeading();
        }

        V segmentAt(int index) {
            return expanded.get(index);
        }

        int distinctIndex(int index) {
            return distinctIndexOfExpanded[index];
        }

        int longestStarting(int index) {
            return depth[index] + 1;
        }

        V transform(int index) {
            List<Integer> fiber = fibers.get(depth[index]);
            int p = Collections.binarySearch(fiber, index);
            if (p < 0) {
                throw new AssertionError("Oracle internal error: index missing from depth fiber.");
            }
            int next = fiber.get((p + 1) % fiber.size());
            return new V(segmentAt(index).b, segmentAt(next).e);
        }

        Map<V, Integer> lBag() {
            Map<V, Integer> result = new TreeMap<>();
            for (List<Integer> fiber : fibers) {
                int j = fiber.get(fiber.size() - 1);
                add(result, transform(j));
            }
            return result;
        }

        Map<V, Integer> derivedBag() {
            Map<V, Integer> result = new TreeMap<>();
            for (int i = 0; i < expanded.size(); i++) {
                if (!distinguished.contains(i)) {
                    add(result, transform(i));
                }
            }
            return result;
        }

        List<Integer> computeLeading() {
            List<Integer> result = new ArrayList<>();
            if (expanded.isEmpty()) {
                return result;
            }

            int minB = expanded.get(0).b;
            V firstValue = null;
            int firstDistinct = -1;

            // First candidate: min b and, among those, minimum e.
            for (int d = 0; d < distinct.size(); d++) {
                V candidate = distinct.get(d);
                if (candidate.b != minB) {
                    break;
                }
                if (firstValue == null || candidate.e < firstValue.e) {
                    firstValue = candidate;
                    firstDistinct = d;
                }
            }

            int currentDistinct = firstDistinct;
            result.add(firstOccurrence[currentDistinct]);

            while (true) {
                V previous = distinct.get(currentDistinct);
                int targetB = previous.b + 1;

                int chosenDistinct = -1;
                V chosen = null;

                for (int d = 0; d < distinct.size(); d++) {
                    V candidate = distinct.get(d);
                    if (candidate.b != targetB) {
                        continue;
                    }
                    if (precedes(previous, candidate)) {
                        if (chosen == null || candidate.e < chosen.e) {
                            chosen = candidate;
                            chosenDistinct = d;
                        }
                    }
                }

                if (chosenDistinct < 0) {
                    break;
                }

                currentDistinct = chosenDistinct;
                result.add(firstOccurrence[currentDistinct]);
            }

            return result;
        }

        Optional<V> deltaStar(int index) {
            V s = segmentAt(index);
            if (!leading.contains(index)) {
                return Optional.of(s);
            }
            if (s.b == s.e) {
                return Optional.empty();
            }
            return Optional.of(new V(s.b + 1, s.e));
        }

        Map<V, Integer> mCrossBag() {
            Map<V, Integer> result = new TreeMap<>();
            for (int i = 0; i < expanded.size(); i++) {
                Optional<V> ds = deltaStar(i);
                if (ds.isPresent()) {
                    add(result, ds.get());
                }
            }
            return result;
        }

        V deltaCircle() {
            int min = expanded.get(0).b;
            return new V(min, min + leading.size() - 1);
        }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 6) {
            System.err.println(
                "Usage: ComprehensiveRandomTester " +
                "SAMPLES|all ENDPOINT_BOUND MAX_DISTINCT MAX_MULTIPLICITY " +
                "MAX_TOTAL_CARDINALITY SEED"
            );
            System.err.println();
            System.err.println("Examples:");
            System.err.println("  10000 20 4 2 5 12345");
            System.err.println("  all 2 3 2 4 12345");
            System.exit(2);
        }

        boolean exhaustive = args[0].equalsIgnoreCase("all");
        int samples = exhaustive ? -1 : positiveInt(args[0], "SAMPLES");
        int endpointBound = nonnegativeInt(args[1], "ENDPOINT_BOUND");
        int maxDistinct = positiveInt(args[2], "MAX_DISTINCT");
        int maxMultiplicity = positiveInt(args[3], "MAX_MULTIPLICITY");
        int maxTotal = positiveInt(args[4], "MAX_TOTAL_CARDINALITY");
        long seed = Long.parseLong(args[5]);

        List<V> universe = segmentUniverse(endpointBound);
        int effectiveDistinct =
            Math.min(maxDistinct, Math.min(maxTotal, universe.size()));

        BigInteger theoretical =
            theoreticalBagCount(
                universe.size(),
                effectiveDistinct,
                maxMultiplicity,
                maxTotal
            );

        if (!exhaustive && BigInteger.valueOf(samples).compareTo(theoretical) > 0) {
            throw new IllegalArgumentException(
                "Requested " + samples + " distinct multisegments, but only " +
                theoretical + " exist under these bounds."
            );
        }

        if (exhaustive && theoretical.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0) {
            throw new IllegalArgumentException(
                "Exhaustive mode would require checking " + theoretical +
                " multisegments, which exceeds this tester's counter range. " +
                "Use tighter bounds."
            );
        }

        System.out.println();
        System.out.println("============================================================");
        System.out.println(
            exhaustive
                ? "Comprehensive Java exhaustive test"
                : "Comprehensive Java randomized test"
        );
        System.out.println("Mode                     = " + (exhaustive ? "ALL" : "RANDOM"));
        if (!exhaustive) {
            System.out.println("Samples                  = " + samples);
        }
        System.out.println(
            "Endpoint range           = -" + endpointBound + ".." + endpointBound
        );
        System.out.println(
            "Possible segment values  = " + universe.size()
        );
        System.out.println(
            "Distinct segments        = 1.." + effectiveDistinct
        );
        System.out.println(
            "Multiplicity per segment = 1.." + maxMultiplicity
        );
        System.out.println(
            "Total cardinality cap    = " + maxTotal
        );
        System.out.println("Seed                     = " + seed);
        System.out.println(
            "Theoretical multisegments= " + theoretical
        );
        System.out.println("============================================================");
        System.out.println();

        // Segment-level checks are independent of the multisegment mode.
        testSegmentClass(universe, endpointBound, seed);

        // Edge-case behavior of the empty multisegment.
        testEmptyMultisegment();

        long checkedCases;

        if (exhaustive) {
            long totalCases = theoretical.longValueExact();
            long progressStep = Math.max(1L, totalCases / 10L);
            long[] generated = {0L};
            Random constructorOrderRandom = new Random(seed);

            enumerateAllCases(
                universe,
                effectiveDistinct,
                maxMultiplicity,
                maxTotal,
                constructorOrderRandom,
                c -> {
                    generated[0]++;
                    try {
                        testOne(c.constructorInput);
                    } catch (Throwable failure) {
                        System.err.println();
                        System.err.println("============================================================");
                        System.err.println("FAIL");
                        System.err.println("Case number   = " + generated[0]);
                        System.err.println("Mode          = ALL");
                        System.err.println("Input         = " + c.key);
                        System.err.println("============================================================");
                        throw failure;
                    }

                    if (
                        generated[0] % progressStep == 0 ||
                        generated[0] == totalCases
                    ) {
                        System.out.println(
                            "Checked " + generated[0] + " / " + totalCases +
                            " multisegments..."
                        );
                    }
                }
            );

            checkedCases = generated[0];
            if (checkedCases != totalCases) {
                throw new AssertionError(
                    "Exhaustive generator produced " + checkedCases +
                    " cases, but the theoretical count is " + totalCases + "."
                );
            }
        } else {
            Random random = new Random(seed);
            Set<String> seen = new HashSet<>();
            int generated = 0;
            int attempts = 0;
            int maxAttempts = Math.max(10000, samples * 1000);

            while (generated < samples) {
                if (++attempts > maxAttempts) {
                    throw new IllegalStateException(
                        "Could not generate enough distinct random cases efficiently. " +
                        "Try wider bounds or request fewer samples."
                    );
                }

                GeneratedCase c =
                    generateCase(
                        random,
                        universe,
                        effectiveDistinct,
                        maxMultiplicity,
                        maxTotal
                    );

                if (!seen.add(c.key)) {
                    continue;
                }

                generated++;
                try {
                    testOne(c.constructorInput);
                } catch (Throwable failure) {
                    System.err.println();
                    System.err.println("============================================================");
                    System.err.println("FAIL");
                    System.err.println("Sample number = " + generated);
                    System.err.println("Seed          = " + seed);
                    System.err.println("Input         = " + c.key);
                    System.err.println("============================================================");
                    throw failure;
                }

                if (generated % Math.max(1, samples / 10) == 0 || generated == samples) {
                    System.out.println(
                        "Checked " + generated + " / " + samples + " multisegments..."
                    );
                }
            }

            checkedCases = generated;
        }

        System.out.println();
        System.out.println("============================================================");
        System.out.println("ALL JAVA TESTS PASSED");
        System.out.println("Mode                         = " + (exhaustive ? "ALL" : "RANDOM"));
        System.out.println("Distinct multisegments checked = " + checkedCases);
        System.out.println("Individual assertions checked  = " + checks);
        System.out.println(
            "Non-vacuous Lemma/Corollary cases = " + corollaryCases +
            " / " + checkedCases
        );
        System.out.println("Seed = " + seed);
        System.out.println("============================================================");
    }

    private static void testOne(Segment[] input) throws Exception {
        MultiSegment m = new MultiSegment(input);
        Oracle o = new Oracle(input);

        check(m.size() == o.expanded.size(), "size() is incorrect.");

        // ----- private cached representation data -----
        check(
            vList(reflectDistinct(m)).equals(o.distinct),
            "distinctSegments() does not equal the sorted distinct segment list."
        );

        check(
            reflectCumulative(m).equals(o.cumulative),
            "cumulativeFreq() is incorrect."
        );

        check(
            Arrays.equals(reflectLongest(m), o.longestDistinct),
            "longestStarting() is incorrect."
        );

        List<List<Integer>> javaFibers = reflectEnumerations(m);
        check(
            javaFibers.equals(o.fibers),
            "admissibleEnumerations() does not match the independently computed depth fibers."
        );

        // Each returned enumeration must independently be admissible.
        for (int k = 0; k < javaFibers.size(); k++) {
            List<Integer> fiber = javaFibers.get(k);
            check(!fiber.isEmpty(), "An admissible depth fiber is unexpectedly empty.");

            Set<Integer> unique = new HashSet<>(fiber);
            check(
                unique.size() == fiber.size(),
                "Admissible enumeration contains a repeated global index."
            );

            for (int p = 0; p < fiber.size(); p++) {
                int index = fiber.get(p);
                check(
                    o.depth[index] == k,
                    "Admissible enumeration contains an index of the wrong depth."
                );
                if (p > 0) {
                    int prev = fiber.get(p - 1);
                    check(
                        prev < index,
                        "Admissible enumeration is not in increasing global-index order."
                    );
                    check(
                        subsetEq(o.segmentAt(index), o.segmentAt(prev)),
                        "Admissible enumeration violates containment."
                    );
                }
            }
        }

        // ----- global indexing, depths, transforms -----
        for (int i = 0; i < o.expanded.size(); i++) {
            check(
                m.distinctIndex(i) == o.distinctIndex(i),
                "distinctIndex(" + i + ") is incorrect."
            );

            check(
                v(reflectSegmentAt(m, i)).equals(o.segmentAt(i)),
                "segmentAt(" + i + ") is incorrect."
            );

            check(
                m.longestChainStartingAt(i) == o.longestStarting(i),
                "longestChainStartingAt(" + i + ") is incorrect."
            );

            check(
                m.depth(i) == o.depth[i],
                "depth(" + i + ") is incorrect."
            );

            check(
                v(m.SegmentTransform(i)).equals(o.transform(i)),
                "SegmentTransform(" + i + ") is incorrect."
            );

            Optional<V> actualDeltaStar = reflectDeltaStar(m, i);
            check(
                actualDeltaStar.equals(o.deltaStar(i)),
                "deltaStar(" + i + ") is incorrect."
            );
        }

        for (int d = 0; d < o.distinct.size(); d++) {
            check(
                m.firstOccurrenceIndex(d) == o.firstOccurrence[d],
                "firstOccurrenceIndex(" + d + ") is incorrect."
            );
        }

        check(
            m.DistinguishedIndices().equals(o.distinguished),
            "DistinguishedIndices() is incorrect."
        );

        Map<V, Integer> actualL = bagOf(m.l());
        check(
            actualL.equals(o.lBag()),
            "l() has the wrong segment multiplicities."
        );
        check(
            isLadder(actualL),
            "l() is not a ladder."
        );

        Map<V, Integer> actualDerived = bagOf(m.DerivedMultisegment());
        check(
            actualDerived.equals(o.derivedBag()),
            "DerivedMultisegment() is incorrect."
        );

        // ----- Definition 3.1 / MW construction -----
        List<Integer> actualLeading = m.LeadingIndices();
        check(
            actualLeading.equals(o.leading),
            "LeadingIndices() does not match the independent construction."
        );
        check(
            validLeadingSequence(o, actualLeading),
            "LeadingIndices() does not satisfy Definition 3.1."
        );

        check(
            v(m.DeltaCircle()).equals(o.deltaCircle()),
            "DeltaCircle() is incorrect."
        );

        Map<V, Integer> actualCross = bagOf(m.MCross());
        check(
            actualCross.equals(o.mCrossBag()),
            "MCross() is incorrect."
        );

        // Repeated calls should be stable and must not mutate the multisegment.
        check(
            bagOf(m.l()).equals(actualL),
            "Repeated l() call changed its result."
        );
        check(
            bagOf(m.DerivedMultisegment()).equals(actualDerived),
            "Repeated DerivedMultisegment() call changed its result."
        );
        check(
            m.LeadingIndices().equals(actualLeading),
            "Repeated LeadingIndices() call changed its result."
        );
        check(
            bagOf(m.MCross()).equals(actualCross),
            "Repeated MCross() call changed its result."
        );

        // ----- Lemma 1 and Corollary 3.4, when hypothesis is true -----
        int minM = o.expanded.get(0).b;
        int minL = minBeginning(actualL);

        if (minM < minL) {
            corollaryCases++;

            MultiSegment derived = m.DerivedMultisegment();
            MultiSegment cross = m.MCross();

            // Lemma 1.
            check(
                derived.size() > 0,
                "Lemma 1 failed: DerivedMultisegment() is empty."
            );
            check(
                cross.size() > 0,
                "Lemma 1 failed: MCross() is empty."
            );

            // Corollary 3.4, componentwise.
            check(
                bagOf(m.l()).equals(bagOf(cross.l())),
                "Corollary failed: l(m) != l(mCross)."
            );

            check(
                v(m.DeltaCircle()).equals(v(derived.DeltaCircle())),
                "Corollary failed: DeltaCircle(m) != DeltaCircle(m')."
            );

            check(
                bagOf(cross.DerivedMultisegment())
                    .equals(bagOf(derived.MCross())),
                "Corollary failed: Derived(MCross(m)) != MCross(Derived(m))."
            );
        }
    }

    private static void testSegmentClass(
        List<V> universe,
        int endpointBound,
        long seed
    ) {
        Segment helper = new Segment(0, 0);

        // Every valid bounded segment.
        for (V value : universe) {
            Segment s = segment(value);

            check(helper.isSegment(s), "isSegment rejects valid segment " + value);

            Set<Integer> expected = new HashSet<>();
            for (int x = value.b; x <= value.e; x++) {
                expected.add(x);
            }
            check(
                helper.segmentToSet(s).equals(expected),
                "segmentToSet is incorrect for " + value
            );

            check(
                s.compareTo(s) == 0,
                "compareTo is not reflexive for " + value
            );
        }

        // Invalid segment should be rejected by isSegment.
        Segment invalid = new Segment(1, 0);
        check(
            !helper.isSegment(invalid),
            "isSegment accepts [1,0]."
        );

        // Deterministic containment check.  This intentionally follows the
        // mathematical/TLA meaning: first argument is contained in second.
        Segment inner = new Segment(1, 1);
        Segment outer = new Segment(0, 2);
        check(
            helper.subsetEq(inner, outer),
            "subsetEq(s1,s2) should mean s1 is contained in s2. " +
            "Expected [1,1] subsetEq [0,2]."
        );
        check(
            !helper.subsetEq(outer, inner),
            "subsetEq direction is reversed."
        );

        // Comparator order across the whole segment universe.
        List<Segment> javaSorted = new ArrayList<>();
        for (V value : universe) {
            javaSorted.add(segment(value));
        }
        Collections.shuffle(javaSorted, new Random(seed ^ 0x9E3779B97F4A7C15L));
        Collections.sort(javaSorted);

        for (int i = 0; i < javaSorted.size(); i++) {
            check(
                v(javaSorted.get(i)).equals(universe.get(i)),
                "compareTo induces the wrong standard order."
            );
        }

        // Pairwise semantic checks.  Exhaustive for small universes; otherwise
        // use a large reproducible sample to avoid quadratic explosion.
        long pairCount = (long) universe.size() * (long) universe.size();
        Random random = new Random(seed ^ 0xC0FFEE1234L);
        int pairTests =
            pairCount <= 250_000L
                ? (int) pairCount
                : 25_000;

        if (pairCount <= 250_000L) {
            for (V a : universe) {
                for (V b : universe) {
                    checkSegmentPair(helper, a, b);
                }
            }
        } else {
            for (int t = 0; t < pairTests; t++) {
                V a = universe.get(random.nextInt(universe.size()));
                V b = universe.get(random.nextInt(universe.size()));
                checkSegmentPair(helper, a, b);
            }
        }
    }

    private static void checkSegmentPair(Segment helper, V a, V b) {
        Segment sa = segment(a);
        Segment sb = segment(b);

        check(
            sa.precedes(sb) == precedes(a, b),
            "precedes is incorrect for " + a + " and " + b
        );

        check(
            helper.subsetEq(sa, sb) == subsetEq(a, b),
            "subsetEq is incorrect for " + a + " and " + b
        );

        int actualSign = Integer.signum(sa.compareTo(sb));
        int expectedSign = Integer.signum(a.compareTo(b));
        check(
            actualSign == expectedSign,
            "compareTo is incorrect for " + a + " and " + b
        );

        check(
            Integer.signum(sa.compareTo(sb)) == -Integer.signum(sb.compareTo(sa)),
            "compareTo violates antisymmetry for " + a + " and " + b
        );
    }

    private static void testEmptyMultisegment() throws Exception {
        MultiSegment empty = new MultiSegment();

        check(empty.size() == 0, "Empty multisegment has nonzero size.");
        check(
            empty.LeadingIndices().isEmpty(),
            "LeadingIndices() of empty multisegment should be empty."
        );
        check(
            empty.DistinguishedIndices().isEmpty(),
            "DistinguishedIndices() of empty multisegment should be empty."
        );
        check(
            bagOf(empty.l()).isEmpty(),
            "l(empty) should be empty in this Java implementation."
        );
        check(
            bagOf(empty.DerivedMultisegment()).isEmpty(),
            "DerivedMultisegment(empty) should be empty."
        );
        check(
            bagOf(empty.MCross()).isEmpty(),
            "MCross(empty) should be empty."
        );

        boolean threw = false;
        try {
            empty.DeltaCircle();
        } catch (IllegalStateException expected) {
            threw = true;
        }
        check(
            threw,
            "DeltaCircle() should reject an empty multisegment."
        );
    }

    private static boolean validLeadingSequence(
        Oracle o,
        List<Integer> seq
    ) {
        if (seq.isEmpty()) {
            return false;
        }

        for (int index : seq) {
            if (index < 0 || index >= o.expanded.size()) {
                return false;
            }
        }

        int first = seq.get(0);
        V firstSeg = o.segmentAt(first);
        int minB = o.expanded.get(0).b;

        if (firstSeg.b != minB) {
            return false;
        }

        for (V s : o.expanded) {
            if (s.b == minB && firstSeg.e > s.e) {
                return false;
            }
        }

        for (int r = 0; r + 1 < seq.size(); r++) {
            V current = o.segmentAt(seq.get(r));
            V next = o.segmentAt(seq.get(r + 1));

            if (!precedes(current, next)) {
                return false;
            }
            if (next.b != current.b + 1) {
                return false;
            }

            for (V candidate : o.expanded) {
                if (
                    candidate.b == current.b + 1 &&
                    precedes(current, candidate) &&
                    next.e > candidate.e
                ) {
                    return false;
                }
            }
        }

        V last = o.segmentAt(seq.get(seq.size() - 1));
        for (V candidate : o.expanded) {
            if (
                candidate.b == last.b + 1 &&
                precedes(last, candidate)
            ) {
                return false;
            }
        }

        return true;
    }

    private static boolean isLadder(Map<V, Integer> bag) {
        if (bag.isEmpty()) {
            return false;
        }

        // A ladder has no repeated segments.
        for (int count : bag.values()) {
            if (count != 1) {
                return false;
            }
        }

        List<V> values = new ArrayList<>(bag.keySet());
        values.sort(
            Comparator
                .comparingInt((V x) -> x.b)
                .thenComparingInt(x -> x.e)
        );

        for (int i = 0; i + 1 < values.size(); i++) {
            if (!precedes(values.get(i), values.get(i + 1))) {
                return false;
            }
        }
        return true;
    }

    @FunctionalInterface
    private interface CaseConsumer {
        void accept(GeneratedCase c) throws Exception;
    }

    /**
     * Enumerates every nonempty multisegment satisfying the supplied bounds.
     * Each mathematical multisegment (bag) is generated exactly once.
     */
    private static void enumerateAllCases(
        List<V> universe,
        int maxDistinct,
        int maxMultiplicity,
        int maxTotal,
        Random constructorOrderRandom,
        CaseConsumer consumer
    ) throws Exception {
        for (int d = 1; d <= maxDistinct; d++) {
            V[] chosen = new V[d];
            enumerateDistinctChoices(
                universe,
                0,
                0,
                chosen,
                maxMultiplicity,
                maxTotal,
                constructorOrderRandom,
                consumer
            );
        }
    }

    private static void enumerateDistinctChoices(
        List<V> universe,
        int start,
        int depth,
        V[] chosen,
        int maxMultiplicity,
        int maxTotal,
        Random constructorOrderRandom,
        CaseConsumer consumer
    ) throws Exception {
        if (depth == chosen.length) {
            int[] multiplicities = new int[chosen.length];
            enumerateMultiplicities(
                chosen,
                multiplicities,
                0,
                0,
                maxMultiplicity,
                maxTotal,
                constructorOrderRandom,
                consumer
            );
            return;
        }

        int stillNeeded = chosen.length - depth;
        int lastStart = universe.size() - stillNeeded;

        for (int i = start; i <= lastStart; i++) {
            chosen[depth] = universe.get(i);
            enumerateDistinctChoices(
                universe,
                i + 1,
                depth + 1,
                chosen,
                maxMultiplicity,
                maxTotal,
                constructorOrderRandom,
                consumer
            );
        }
    }

    private static void enumerateMultiplicities(
        V[] chosen,
        int[] multiplicities,
        int position,
        int totalSoFar,
        int maxMultiplicity,
        int maxTotal,
        Random constructorOrderRandom,
        CaseConsumer consumer
    ) throws Exception {
        if (position == chosen.length) {
            consumer.accept(
                buildGeneratedCase(
                    Arrays.asList(chosen),
                    multiplicities,
                    constructorOrderRandom
                )
            );
            return;
        }

        // Every remaining distinct segment must occur at least once.
        int remainingAfterThis = chosen.length - position - 1;
        int maxHere =
            Math.min(
                maxMultiplicity,
                maxTotal - totalSoFar - remainingAfterThis
            );

        for (int multiplicity = 1; multiplicity <= maxHere; multiplicity++) {
            multiplicities[position] = multiplicity;
            enumerateMultiplicities(
                chosen,
                multiplicities,
                position + 1,
                totalSoFar + multiplicity,
                maxMultiplicity,
                maxTotal,
                constructorOrderRandom,
                consumer
            );
        }
    }

    private static GeneratedCase generateCase(
        Random random,
        List<V> universe,
        int maxDistinct,
        int maxMultiplicity,
        int maxTotal
    ) {
        int d = 1 + random.nextInt(maxDistinct);

        List<Integer> chosenIndices = chooseDistinctIndices(
            random,
            universe.size(),
            d
        );

        List<V> chosen = new ArrayList<>();
        for (int index : chosenIndices) {
            chosen.add(universe.get(index));
        }
        Collections.sort(chosen);

        int[] multiplicities = new int[d];
        Arrays.fill(multiplicities, 1);

        int remainingCapacity = maxTotal - d;
        for (int i = 0; i < d; i++) {
            int maxExtra = Math.min(maxMultiplicity - 1, remainingCapacity);
            int extra = maxExtra == 0 ? 0 : random.nextInt(maxExtra + 1);
            multiplicities[i] += extra;
            remainingCapacity -= extra;
        }

        return buildGeneratedCase(chosen, multiplicities, random);
    }

    private static GeneratedCase buildGeneratedCase(
        List<V> chosen,
        int[] multiplicities,
        Random constructorOrderRandom
    ) {
        List<Segment> expanded = new ArrayList<>();
        StringBuilder key = new StringBuilder();

        for (int i = 0; i < chosen.size(); i++) {
            V value = chosen.get(i);
            if (i > 0) {
                key.append(" ; ");
            }
            key.append(value).append(" x").append(multiplicities[i]);

            for (int r = 0; r < multiplicities[i]; r++) {
                expanded.add(segment(value));
            }
        }

        // The mathematical case is a bag, so constructor order is irrelevant.
        // We still shuffle deterministically to exercise insertion-order independence.
        Collections.shuffle(expanded, constructorOrderRandom);

        return new GeneratedCase(
            expanded.toArray(new Segment[0]),
            key.toString()
        );
    }

    private static List<Integer> chooseDistinctIndices(
        Random random,
        int universeSize,
        int count
    ) {
        Set<Integer> selected = new LinkedHashSet<>();
        while (selected.size() < count) {
            selected.add(random.nextInt(universeSize));
        }
        return new ArrayList<>(selected);
    }

    private static List<V> segmentUniverse(int bound) {
        List<V> result = new ArrayList<>();
        for (int b = -bound; b <= bound; b++) {
            for (int e = b; e <= bound; e++) {
                result.add(new V(b, e));
            }
        }
        Collections.sort(result);
        return result;
    }

    private static BigInteger theoreticalBagCount(
        int segmentValues,
        int maxDistinct,
        int maxMultiplicity,
        int maxTotal
    ) {
        BigInteger total = BigInteger.ZERO;

        for (int d = 1; d <= maxDistinct; d++) {
            BigInteger choose = binomial(segmentValues, d);
            BigInteger multiplicityPatterns =
                multiplicityPatternCount(
                    d,
                    maxMultiplicity,
                    maxTotal
                );
            total = total.add(choose.multiply(multiplicityPatterns));
        }

        return total;
    }

    private static BigInteger multiplicityPatternCount(
        int d,
        int maxMultiplicity,
        int maxTotal
    ) {
        BigInteger[][] dp = new BigInteger[d + 1][maxTotal + 1];
        for (int i = 0; i <= d; i++) {
            Arrays.fill(dp[i], BigInteger.ZERO);
        }
        dp[0][0] = BigInteger.ONE;

        for (int i = 0; i < d; i++) {
            for (int sum = 0; sum <= maxTotal; sum++) {
                if (dp[i][sum].signum() == 0) {
                    continue;
                }
                for (int mult = 1; mult <= maxMultiplicity; mult++) {
                    if (sum + mult <= maxTotal) {
                        dp[i + 1][sum + mult] =
                            dp[i + 1][sum + mult].add(dp[i][sum]);
                    }
                }
            }
        }

        BigInteger result = BigInteger.ZERO;
        for (int sum = 1; sum <= maxTotal; sum++) {
            result = result.add(dp[d][sum]);
        }
        return result;
    }

    private static BigInteger binomial(int n, int k) {
        if (k < 0 || k > n) {
            return BigInteger.ZERO;
        }
        k = Math.min(k, n - k);
        BigInteger result = BigInteger.ONE;
        for (int i = 1; i <= k; i++) {
            result =
                result
                    .multiply(BigInteger.valueOf(n - k + i))
                    .divide(BigInteger.valueOf(i));
        }
        return result;
    }

    private static Map<V, Integer> bagOf(MultiSegment m) throws Exception {
        List<Segment> distinct = reflectDistinct(m);
        List<Integer> cumulative = reflectCumulative(m);

        Map<V, Integer> result = new TreeMap<>();
        int previous = 0;
        for (int i = 0; i < distinct.size(); i++) {
            int current = cumulative.get(i);
            result.put(v(distinct.get(i)), current - previous);
            previous = current;
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static List<Segment> reflectDistinct(MultiSegment m)
        throws Exception {
        return (List<Segment>) distinctSegmentsMethod.invoke(m);
    }

    @SuppressWarnings("unchecked")
    private static List<Integer> reflectCumulative(MultiSegment m)
        throws Exception {
        return (List<Integer>) cumulativeFreqMethod.invoke(m);
    }

    private static int[] reflectLongest(MultiSegment m)
        throws Exception {
        return (int[]) longestStartingMethod.invoke(m);
    }

    @SuppressWarnings("unchecked")
    private static List<List<Integer>> reflectEnumerations(MultiSegment m)
        throws Exception {
        return (List<List<Integer>>) admissibleEnumerationsMethod.invoke(m);
    }

    private static Segment reflectSegmentAt(MultiSegment m, int i)
        throws Exception {
        return (Segment) segmentAtMethod.invoke(m, i);
    }

    @SuppressWarnings("unchecked")
    private static Optional<V> reflectDeltaStar(MultiSegment m, int i)
        throws Exception {
        Optional<Segment> value =
            (Optional<Segment>) deltaStarMethod.invoke(m, i);
        if (value.isPresent()) {
            return Optional.of(v(value.get()));
        }
        return Optional.empty();
    }

    private static int minBeginning(Map<V, Integer> bag) {
        if (bag.isEmpty()) {
            throw new IllegalArgumentException("Cannot take min of empty bag.");
        }
        int min = Integer.MAX_VALUE;
        for (V s : bag.keySet()) {
            min = Math.min(min, s.b);
        }
        return min;
    }

    private static List<V> vList(List<Segment> values) {
        List<V> result = new ArrayList<>();
        for (Segment s : values) {
            result.add(v(s));
        }
        return result;
    }

    private static V v(Segment s) {
        return new V(s.b, s.e);
    }

    private static Segment segment(V value) {
        return new Segment(value.b, value.e);
    }

    private static boolean precedes(V a, V b) {
        return a.b < b.b && a.e < b.e;
    }

    /**
     * Mathematical meaning: first argument is contained in second.
     */
    private static boolean subsetEq(V inner, V outer) {
        return outer.b <= inner.b && inner.e <= outer.e;
    }

    private static void add(Map<V, Integer> bag, V value) {
        bag.put(value, bag.getOrDefault(value, 0) + 1);
    }

    private static void check(boolean condition, String message) {
        checks++;
        if (!condition) {
            throw new AssertionError(message);
        }
    }

    private static int positiveInt(String raw, String name) {
        int value = Integer.parseInt(raw);
        if (value <= 0) {
            throw new IllegalArgumentException(name + " must be positive.");
        }
        return value;
    }

    private static int nonnegativeInt(String raw, String name) {
        int value = Integer.parseInt(raw);
        if (value < 0) {
            throw new IllegalArgumentException(name + " must be nonnegative.");
        }
        return value;
    }
}
