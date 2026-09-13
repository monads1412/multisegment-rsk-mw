#!/usr/bin/env python3

import argparse
import math
import random
from pathlib import Path


def parse_args():
    p = argparse.ArgumentParser(
        description=(
            "Generate one reproducible set of random mathematical multisegments "
            "and materialize it for both TLA+ representations."
        )
    )
    p.add_argument("sample_count", type=int)
    p.add_argument("endpoint_bound", type=int)
    p.add_argument("max_distinct_segments", type=int)
    p.add_argument("max_multiplicity", type=int)
    p.add_argument("max_total_cardinality", type=int)
    p.add_argument("seed", type=int)
    p.add_argument("--sequence-template", default="RandomSequenceTestsTemplate.tla")
    p.add_argument("--bag-template", default="RandomBagTestsTemplate.tla")
    p.add_argument("--sequence-output", default="RandomSequenceTests.tla")
    p.add_argument("--bag-output", default="RandomBagTests.tla")
    return p.parse_args()


def multiplicity_vector_count(k: int, max_multiplicity: int, max_total: int) -> int:
    """Count vectors (m1,...,mk) with 1<=mi<=M and sum(mi)<=T."""
    # DP by number of entries and total sum.
    dp = [0] * (max_total + 1)
    dp[0] = 1
    for _ in range(k):
        nxt = [0] * (max_total + 1)
        for total, count in enumerate(dp):
            if count == 0:
                continue
            for mult in range(1, max_multiplicity + 1):
                if total + mult <= max_total:
                    nxt[total + mult] += count
        dp = nxt
    return sum(dp)


def descriptor_to_bag_tla(bag):
    entries = [
        f"<<Segment({left}, {right}), {multiplicity}>>"
        for left, right, multiplicity in bag
    ]
    return "<< " + ", ".join(entries) + " >>"


def descriptor_to_sequence_tla(bag, rng):
    occurrences = []
    for left, right, multiplicity in bag:
        occurrences.extend([(left, right)] * multiplicity)
    rng.shuffle(occurrences)
    return "<<" + ", ".join(
        f"Segment({left}, {right})" for left, right in occurrences
    ) + ">>"


def main():
    args = parse_args()

    positive_fields = {
        "sample_count": args.sample_count,
        "endpoint_bound": args.endpoint_bound,
        "max_distinct_segments": args.max_distinct_segments,
        "max_multiplicity": args.max_multiplicity,
        "max_total_cardinality": args.max_total_cardinality,
    }
    for name, value in positive_fields.items():
        if value <= 0:
            raise SystemExit(f"{name} must be a positive integer")

    B = args.endpoint_bound
    segments = [
        (left, right)
        for left in range(-B, B + 1)
        for right in range(left, B + 1)
    ]

    max_distinct = min(
        args.max_distinct_segments,
        args.max_total_cardinality,
        len(segments),
    )

    if max_distinct <= 0:
        raise SystemExit("No feasible nonempty multisegment under these bounds")

    vector_counts = {
        k: multiplicity_vector_count(
            k,
            args.max_multiplicity,
            args.max_total_cardinality,
        )
        for k in range(1, max_distinct + 1)
    }
    feasible_support_sizes = [k for k, count in vector_counts.items() if count > 0]

    possible_multisegments = sum(
        math.comb(len(segments), k) * vector_counts[k]
        for k in feasible_support_sizes
    )

    if args.sample_count > possible_multisegments:
        raise SystemExit(
            f"Requested {args.sample_count} distinct mathematical multisegments, "
            f"but only {possible_multisegments} are possible with these bounds."
        )

    rng = random.Random(args.seed)
    samples = set()
    attempts = 0
    max_attempts = max(100_000, args.sample_count * 10_000)

    # Coverage-oriented rather than universe-uniform: choose support size
    # uniformly first, so small supports are not drowned out by the huge
    # number of large-support combinations.
    while len(samples) < args.sample_count:
        attempts += 1
        if attempts > max_attempts:
            raise SystemExit(
                "Could not obtain enough distinct samples efficiently. "
                "Try a larger endpoint bound or looser size bounds."
            )

        k = rng.choice(feasible_support_sizes)
        support = rng.sample(segments, k)

        # Draw multiplicities until the total-cardinality cap is respected.
        multiplicities = None
        for _ in range(1000):
            candidate = [rng.randint(1, args.max_multiplicity) for _ in range(k)]
            if sum(candidate) <= args.max_total_cardinality:
                multiplicities = candidate
                break
        if multiplicities is None:
            continue

        bag = tuple(sorted(
            (left, right, mult)
            for (left, right), mult in zip(support, multiplicities)
        ))
        samples.add(bag)

    samples = sorted(samples)

    # Use a separate RNG stream for sequence order, so changing formatting or
    # sampling internals does not accidentally perturb mathematical samples.
    order_rng = random.Random(args.seed ^ 0x5EED5EED)

    sequence_samples = ",\n".join(
        "    " + descriptor_to_sequence_tla(bag, order_rng)
        for bag in samples
    )
    bag_descriptors = ",\n".join(
        "    " + descriptor_to_bag_tla(bag)
        for bag in samples
    )

    base = Path(__file__).resolve().parent
    replacements = {
        "__SAMPLE_COUNT__": str(args.sample_count),
        "__ENDPOINT_BOUND__": str(args.endpoint_bound),
        "__MAX_DISTINCT_SEGMENTS__": str(max_distinct),
        "__MAX_MULTIPLICITY__": str(args.max_multiplicity),
        "__MAX_TOTAL_CARDINALITY__": str(args.max_total_cardinality),
        "__RANDOM_SEED__": str(args.seed),
        "__SEQUENCE_SAMPLES__": sequence_samples,
        "__BAG_DESCRIPTORS__": bag_descriptors,
    }

    for template_name, output_name in [
        (args.sequence_template, args.sequence_output),
        (args.bag_template, args.bag_output),
    ]:
        text = (base / template_name).read_text(encoding="utf-8")
        for old, new in replacements.items():
            text = text.replace(old, new)
        (base / output_name).write_text(text, encoding="utf-8")

    total_cards = [sum(mult for _, _, mult in bag) for bag in samples]
    supports = [len(bag) for bag in samples]
    multiplicities_seen = [
        mult for bag in samples for _, _, mult in bag
    ]

    print(f"Generated exactly {len(samples)} distinct mathematical multisegments.")
    print(f"Possible segment values: {len(segments)}")
    print(f"Endpoint range: {-B}..{B}")
    print(f"Distinct segments allowed: 1..{max_distinct}")
    print(f"Multiplicity allowed: 1..{args.max_multiplicity}")
    print(f"Total cardinality allowed: 1..{args.max_total_cardinality}")
    print(f"Observed distinct-segment count: {min(supports)}..{max(supports)}")
    print(f"Observed multiplicity: {min(multiplicities_seen)}..{max(multiplicities_seen)}")
    print(f"Observed total cardinality: {min(total_cards)}..{max(total_cards)}")
    print(f"Theoretical mathematical multisegments under bounds: {possible_multisegments}")
    print(f"Seed: {args.seed}")
    print("Wrote RandomSequenceTests.tla and RandomBagTests.tla")


if __name__ == "__main__":
    main()
