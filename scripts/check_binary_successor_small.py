#!/usr/bin/env python3
"""Exhaustive finite audit of binary linear boring-coordinate codes.

For a chosen increasing set of pivot positions in F_2^N, the pivot
coordinates equal the source coordinates. Each non-pivot coordinate is
an arbitrary linear combination of earlier pivot coordinates.

Check that these codes realise every d-dimensional subspace for N <= 5,
and that every subspace of a represented D-space is the image of such a
code composed inside F_2^D for N <= 4.

This is a regression audit, NOT a formal or general proof of GLR.
"""
from itertools import combinations, product


def span(vectors):
    result = {0}
    for v in vectors:
        result |= {x ^ v for x in tuple(result)}
    return frozenset(result)


def all_subspaces(n, d):
    if d == 0:
        return {frozenset([0])}
    return {
        space
        for vectors in combinations(range(1, 1 << n), d)
        if len(space := span(vectors)) == 1 << d
    }


def linear_codes(n, d):
    for pivots in combinations(range(n), d):
        nonpivots = [j for j in range(n) if j not in pivots]
        options = [
            range(1 << sum(p < j for p in pivots))
            for j in nonpivots
        ]
        for choices in product(*options):
            rows = []
            for i in range(d):
                row = 0
                for j in range(n):
                    if j in pivots:
                        if pivots.index(j) == i:
                            row |= 1 << j
                    else:
                        earlier = sum(p < j for p in pivots)
                        ix = nonpivots.index(j)
                        if i < earlier and (choices[ix] >> i) & 1:
                            row |= 1 << j
                rows.append(row)
            yield rows


def check_range_coverage():
    for n in range(6):
        for d in range(n + 1):
            target = all_subspaces(n, d)
            represented = {span(rows) for rows in linear_codes(n, d)}
            assert target == represented, (n, d, target - represented)
            print(f"PASS N={n} d={d}: {len(target)} subspaces")


def check_factorisation():
    for n in range(5):
        for d in range(n + 1):
            codes = list(linear_codes(n, d))
            realised_by_dimension = [
                {span(rows) for rows in linear_codes(d, a)}
                for a in range(d + 1)
            ]
            for rows in codes:
                images = {}
                for x in range(1 << d):
                    val = 0
                    for i in range(d):
                        if (x >> i) & 1:
                            val ^= rows[i]
                    images[x] = val
                W = frozenset(images.values())
                for a in range(d + 1):
                    for P in all_subspaces(n, a):
                        if P.issubset(W):
                            preimage = frozenset(
                                x for x, y in images.items() if y in P
                            )
                            assert preimage in realised_by_dimension[a], (
                                n, d, a, rows, P
                            )
            print(f"PASS factor N={n} D={d}: {len(codes)} embeddings")


if __name__ == "__main__":
    check_range_coverage()
    check_factorisation()
    print("ALL SMALL-DIMENSIONAL CHECKS PASSED")
