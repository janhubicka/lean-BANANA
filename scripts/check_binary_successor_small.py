#!/usr/bin/env python3
"""Exhaustive finite audit of binary linear boring-coordinate codes.

For a chosen increasing set of pivot positions in F_2^N, the pivot
coordinates equal the source coordinates. Each non-pivot coordinate is
an arbitrary linear combination of earlier pivot coordinates.

Check that these codes realise every d-dimensional subspace for N <= 5,
and that every subspace of a represented D-space is the image of such a
code composed inside F_2^D for N <= 4. The last-coordinate induction is
checked for every binary subspace through ambient dimension seven.

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




def check_skipped_coordinate_contraction():
    # Inspect every penultimate skipped level in each finite row-echelon
    # prefix map. The deleted coordinate is a linear functional of the
    # prefix, and reinsertion must recover the original images.
    for n in range(6):
        for d in range(n + 1):
            for pivots in combinations(range(n), d):
                nonpivots = [j for j in range(n) if j not in pivots]
                choices = [
                    range(1 << sum(p < j for p in pivots))
                    for j in nonpivots
                ]
                for choice in product(*choices):
                    levels = list(pivots) + [n]

                    def prefix_image(i, x):
                        value = 0
                        for j in range(levels[i]):
                            if j in pivots[:i]:
                                bit = (x >> pivots.index(j)) & 1
                            else:
                                coef = choice[nonpivots.index(j)]
                                bit = (coef & x).bit_count() & 1
                            value |= bit << j
                        return value

                    for i in range(d + 1):
                        t = levels[i] - 1
                        if levels[i] == 0 or t in levels:
                            continue
                        assert t not in pivots[:i]
                        coef = choice[nonpivots.index(t)]
                        for j in range(i + 1):
                            for x in range(1 << j):
                                value = prefix_image(j, x)
                                if levels[j] <= t:
                                    continue
                                prefix = value & ((1 << t) - 1)
                                inserted_bit = 0
                                for k, p in enumerate(pivots[:i]):
                                    if p < t and (coef >> k) & 1:
                                        inserted_bit ^= (prefix >> p) & 1
                                erased = (
                                    (value & ((1 << t) - 1)) |
                                    ((value >> (t + 1)) << t)
                                )
                                restored = (
                                    (erased & ((1 << t) - 1)) |
                                    (inserted_bit << t) |
                                    ((erased >> t) << (t + 1))
                                )
                                assert restored == value, (
                                    n, d, pivots, choice, i, j, x, t
                                )
    print("PASS M2 reinsertion for all row-echelon codes, N <= 5")

def check_last_coordinate_induction():
    """Audit the pivot/boring decomposition for every subspace through N=7.

    The vertical unit lies in P exactly in the pivot case. Otherwise P is
    the graph of a linear functional on its projected subspace, and that
    functional must extend to all earlier coordinates.
    """
    expected_counts = (1, 2, 5, 16, 67, 374, 2825, 29212)
    for n in range(8):
        checked = pivot = dependent = 0
        for d in range(n + 1):
            for rows in linear_codes(n, d):
                P = span(rows)
                assert len(P) == 1 << d
                checked += 1
                if n == 0:
                    continue
                mask = (1 << (n - 1)) - 1
                vertical = 1 << (n - 1)
                Q = {v & mask for v in P}
                if vertical in P:
                    pivot += 1
                    assert len(Q) * 2 == len(P)
                    assert P == frozenset(
                        q | b * vertical
                        for q in Q for b in (0, 1)
                    )
                    assert d == (len(Q).bit_length() - 1) + 1
                else:
                    dependent += 1
                    assert len(P) == len(Q)
                    assert d == len(Q).bit_length() - 1
                    graph = {v & mask: v >> (n - 1) for v in P}
                    assert len(graph) == len(Q)
                    assert all(
                        graph[a ^ b] == (graph[a] ^ graph[b])
                        for a in Q for b in Q
                    )
                    assert any(
                        all(((q & e).bit_count() & 1) == graph[q] for q in Q)
                        for e in range(1 << (n - 1))
                    ), (n, d, rows)
        assert checked == expected_counts[n], (n, checked)
        print(
            f"PASS last-coordinate N={n}: {checked} subspaces, "
            f"{pivot} pivots, {dependent} dependent"
        )


if __name__ == "__main__":
    check_range_coverage()
    check_factorisation()
    check_skipped_coordinate_contraction()
    check_last_coordinate_induction()
    print("ALL SMALL-DIMENSIONAL CHECKS PASSED")
