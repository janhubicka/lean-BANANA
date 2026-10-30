#!/usr/bin/env python3
"""Independent finite adversarial checks for BANANA's symplectic application.

This is a regression check, not a proof of the general residue lemma.
No external dependencies, and no GitHub Actions required.
"""
from collections import Counter
from itertools import combinations
from math import comb
from random import Random


def rank_f2(rows: list[int], dimension: int) -> int:
    rows = rows.copy()
    rank = 0
    for column in range(dimension):
        pivot = next((i for i in range(rank, dimension) if rows[i] & (1 << column)), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for i in range(dimension):
            if i != rank and rows[i] & (1 << column):
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def polar_rank(q_values: list[int], dimension: int) -> int:
    rows = [0] * dimension
    for i in range(dimension):
        for j in range(dimension):
            b = (q_values[0] + q_values[1 << i] + q_values[1 << j]
                 + q_values[(1 << i) ^ (1 << j)]) % 2
            rows[i] |= b << j
    return rank_f2(rows, dimension)


def verify_counts(q_values: list[int], modulus: int) -> None:
    counts = Counter(value % modulus for value in q_values)
    assert all(counts[r] % 2 == 1 for r in range(modulus)), counts


def canonical_example(modulus: int) -> tuple[list[int], list[int]]:
    d = modulus - 1
    dimension = 2 * d
    values = [sum(((z >> (2 * j)) & 1) * ((z >> (2 * j + 1)) & 1)
                  for j in range(d)) for z in range(1 << dimension)]
    assert polar_rank(values, dimension) == dimension
    verify_counts(values, modulus)
    moments = [sum(comb(value, k) if k <= value else 0 for value in values)
               for k in range(d + 1)]
    for k in range(d):
        assert moments[k] % (1 << (2 * d - 2 * k)) == 0
        assert ((-2) ** k * moments[k]) % (1 << (d + 1)) == 0
    assert moments[d] % 2 == 1
    return values, moments


def exhaustive_six_dimensional() -> int:
    dimension = 6
    pairs = list(combinations(range(dimension), 2))
    checked = 0
    for edges_mask in range(1 << len(pairs)):
        rows = [0] * dimension
        edges = [pair for k, pair in enumerate(pairs) if edges_mask & (1 << k)]
        for i, j in edges:
            rows[i] ^= 1 << j
            rows[j] ^= 1 << i
        if rank_f2(rows, dimension) != dimension:
            continue
        q_values = [sum(((z >> i) & 1) * ((z >> j) & 1)
                        for i, j in edges) for z in range(1 << dimension)]
        verify_counts(q_values, 4)
        checked += 1
    return checked


def sampled_affine_products(seed: int = 20261028, trials: int = 400) -> int:
    rng = Random(seed)
    dimension = 6
    checked = 0
    for _ in range(trials):
        terms = [(rng.randrange(1 << dimension), rng.randrange(2),
                  rng.randrange(1 << dimension), rng.randrange(2))
                 for _ in range(rng.randrange(9, 25))]
        q_values = []
        for z in range(1 << dimension):
            q_values.append(sum((((a & z).bit_count() + a0) % 2)
                                * (((b & z).bit_count() + b0) % 2)
                                for a, a0, b, b0 in terms))
        if polar_rank(q_values, dimension) == dimension:
            verify_counts(q_values, 4)
            checked += 1
    return checked


def high_moment_counterexample() -> None:
    """Nondegenerate q=4 example where M_4 is not divisible by 2^(d+1).

    The original proof overstates the divisibility of M_k itself when k>d.
    Only the weighted term (-2)^k M_k must have that divisibility.
    """
    dimension = 6
    values = [
        3 * ((z >> 0) & 1) * ((z >> 1) & 1)
        + ((z >> 2) & 1) * ((z >> 3) & 1)
        + ((z >> 4) & 1) * ((z >> 5) & 1)
        for z in range(1 << dimension)
    ]
    assert polar_rank(values, dimension) == dimension
    verify_counts(values, 4)
    moment_four = sum(comb(value, 4) if value >= 4 else 0 for value in values)
    assert moment_four == 11
    assert moment_four % 16 != 0
    assert ((-2) ** 4 * moment_four) % 16 == 0


def main() -> None:
    for modulus in (2, 4, 8):
        values, moments = canonical_example(modulus)
        counts = Counter(value % modulus for value in values)
        print(f"q={modulus}: {len(values)} inputs, residue counts "
              f"{[counts[i] for i in range(modulus)]}, M_{{q-1}}={moments[modulus-1]}")
    _, m = canonical_example(4)
    assert m[1] == 48 and m[1] % 32 != 0, "lost counterexample to overstated bound"
    print("q=4: M_1=48 disproves the manuscript's 32-divisibility claim")
    high_moment_counterexample()
    print("q=4: M_4=11 disproves the high-moment 16-divisibility claim")
    forms = exhaustive_six_dimensional()
    assert forms == 13_888
    print(f"q=4: checked all {forms} nondegenerate alternating six-dimensional forms")
    affine = sampled_affine_products()
    print(f"q=4: checked {affine} random nondegenerate affine-product presentations")
    assert affine > 100
    print("PASS (finite regression only; general proof remains the Lean obligation)")


if __name__ == "__main__":
    main()
