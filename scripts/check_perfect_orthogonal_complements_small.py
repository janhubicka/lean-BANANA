#!/usr/bin/env python3
"""Exhaustive finite adversarial checks of orthogonal BANANA complements.

For every perfect-pair embedding B_m -> B_n with 0 <= m <= n <= 3
over F₂, verify both orthogonal-decomposition retractions on all
ambient vectors. For every ambient pairing automorphism preserving
the two embedded vector subspaces, also verify invariance of the
left/right annihilators. No enumeration choices or nondegeneracy
claims are assumed beyond what is checked.

This is an independent finite-model regression, not a Lean proof
or an independently spawned referee.
"""
from itertools import product


def dot(x: int, y: int) -> int:
    return (x & y).bit_count() & 1


def apply(cols, coeff):
    out = 0
    for i, col in enumerate(cols):
        if (coeff >> i) & 1:
            out ^= col
    return out


def invertibles(n):
    return [
        cols for cols in product(range(1 << n), repeat=n)
        if len({apply(cols, x) for x in range(1 << n)}) == 1 << n
    ]


def contragredient(cols, n):
    return tuple(
        next(y for y in range(1 << n)
             if all(dot(col, y) == (i == j)
                    for i, col in enumerate(cols)))
        for j in range(n)
    )


def run():
    counts = {}
    decompositions = 0
    invariance = 0
    for n in range(4):
        automorphisms = [(h, contragredient(h, n)) for h in invertibles(n)]
        for m in range(n + 1):
            injections = [
                cols for cols in product(range(1 << n), repeat=m)
                if len({apply(cols, x) for x in range(1 << m)}) == 1 << m
            ]
            embeddings = [
                (left, right)
                for left in injections
                for right in injections
                if all(dot(left[i], right[j]) == (i == j)
                       for i in range(m) for j in range(m))
            ]
            counts[n, m] = len(embeddings)
            for left, right in embeddings:
                for v in range(1 << n):
                    left_coeff = sum(dot(v, y) << i for i, y in enumerate(right))
                    right_coeff = sum(dot(x, v) << i for i, x in enumerate(left))
                    zL = v ^ apply(left, left_coeff)
                    zR = v ^ apply(right, right_coeff)
                    assert all(dot(zL, y) == 0 for y in right)
                    assert all(dot(x, zR) == 0 for x in left)
                    assert apply(left, left_coeff) ^ zL == v
                    assert apply(right, right_coeff) ^ zR == v
                    decompositions += 2
                imageL = {apply(left, x) for x in range(1 << m)}
                imageR = {apply(right, x) for x in range(1 << m)}
                for hL, hR in automorphisms:
                    if not (
                        all(apply(hL, x) in imageL for x in imageL)
                        and all(apply(hR, y) in imageR for y in imageR)
                    ):
                        continue
                    for v in range(1 << n):
                        if all(dot(v, y) == 0 for y in right):
                            assert all(dot(apply(hL, v), y) == 0 for y in right)
                            invariance += 1
                        if all(dot(x, v) == 0 for x in left):
                            assert all(dot(x, apply(hR, v)) == 0 for x in left)
                            invariance += 1

    assert counts == {
        (0, 0): 1,
        (1, 0): 1, (1, 1): 1,
        (2, 0): 1, (2, 1): 6, (2, 2): 6,
        (3, 0): 1, (3, 1): 28, (3, 2): 168, (3, 3): 168,
    }
    assert (decompositions, invariance) == (5954, 64664)
    print(
        f"OK: {sum(counts.values())} embeddings, "
        f"{decompositions} decomposition equalities, "
        f"{invariance} complement-invariance equalities"
    )


if __name__ == "__main__":
    run()
