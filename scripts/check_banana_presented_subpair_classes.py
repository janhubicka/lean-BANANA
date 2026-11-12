#!/usr/bin/env python3
"""Separate invariant-vs-explicit-isomorphism audit for finite F2 subpairs.

No imports from the coherent-choice regression or Lean proof sources.
For all pairings with total dimension <= 4, classify subpairs by
(left dimension, right dimension, rank of restricted pairing).
For total dimension <= 3 independently compare that invariant with
an exhaustive two-sorted linear isomorphism search.
Finite testing only: NOT Lean kernel verification.
"""
from collections import defaultdict
from itertools import combinations, product
import json


def vecsum(vectors):
    acc = {0}
    for v in vectors:
        acc |= {w ^ v for w in tuple(acc)}
    return frozenset(acc)


def basis(S):
    selected = []
    span = frozenset((0,))
    for v in sorted(S):
        if v not in span:
            selected.append(v)
            span = vecsum(selected)
    assert span == S
    return tuple(selected)


def spaces(n):
    V = tuple(range(1 << n))
    obtained = {frozenset((0,))}
    for d in range(n + 1):
        for sub in combinations(V[1:], d):
            obtained.add(vecsum(sub))
    return tuple(sorted(obtained, key=lambda x: (len(x), tuple(sorted(x)))))


def parity(v):
    return v.bit_count() & 1


def pairing(rows, x, y):
    return parity(sum(parity(row & y) << i for i, row in enumerate(rows)) & x)


def rank(matrix_rows):
    pivots = {}
    for v in matrix_rows:
        while v:
            pivot = v.bit_length() - 1
            if pivot in pivots:
                v ^= pivots[pivot]
            else:
                pivots[pivot] = v
                break
    return len(pivots)


def signature(rows, SL, SR):
    bL, bR = basis(SL), basis(SR)
    restrictions = [sum(pairing(rows, x, y) << j for j, y in enumerate(bR))
                    for x in bL]
    return (len(bL), len(bR), rank(restrictions))


def invertible_images(S):
    d = len(basis(S))
    return tuple(images for images in product(sorted(S), repeat=d)
                 if vecsum(images) == S)


def explicit_iso(rows, U, V):
    left, right = U
    target_l, target_r = V
    if len(left) != len(target_l) or len(right) != len(target_r):
        return False
    bL, bR = basis(left), basis(right)
    for il in invertible_images(target_l):
        for ir in invertible_images(target_r):
            if all(pairing(rows, bL[i], bR[j]) == pairing(rows, il[i], ir[j])
                   for i in range(len(bL)) for j in range(len(bR))):
                return True
    return False


def run():
    result = defaultdict(int)
    for total in range(5):
        for l in range(total + 1):
            r = total - l
            SS_l, SS_r = spaces(l), spaces(r)
            for rows in product(range(1 << r), repeat=l):
                result["pairings"] += 1
                obj = tuple(product(SS_l, SS_r))
                sig = tuple(signature(rows, *U) for U in obj)
                classes = set(sig)
                result["presented_subpairs"] += len(obj)
                result["iso_classes"] += len(classes)
                if total <= 3:
                    result["iso_classes_total_le_3"] += len(classes)
                    result["subpairs_total_le_3"] += len(obj)
                for U, invariant in zip(obj, sig):
                    assert invariant[0] <= l and invariant[1] <= r
                    assert invariant[0] + invariant[1] <= total
                if total <= 3:
                    for i, U in enumerate(obj):
                        for j, V in enumerate(obj):
                            explicit = explicit_iso(rows, U, V)
                            invariant_equivalent = sig[i] == sig[j]
                            assert explicit == invariant_equivalent, (
                                l, r, rows, i, j, sig[i], sig[j])
                            result["brute_force_pair_comparisons"] += 1
                else:
                    result["dimension_four_pairings"] += 1
    return dict(sorted(result.items()))


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
