#!/usr/bin/env python3
"""Exhaustive low-dimensional audit of one-sided copy/subspace transport.

This checks finite models, not Lean elaboration or kernel correctness.
"""
from itertools import product
from collections import defaultdict


def apply(images, x):
    y = 0
    for i, im in enumerate(images):
        if x >> i & 1:
            y ^= im
    return y


def injective_maps(a, n):
    for images in product(range(1 << n), repeat=a):
        img = [apply(images, x) for x in range(1 << a)]
        if len(set(img)) == 1 << a:
            yield images, frozenset(img)


def all_subspaces(n):
    vs = range(1 << n)
    groups = defaultdict(set)
    for mask in range(1, 1 << (1 << n), 2):
        s = frozenset(v for v in vs if mask >> v & 1)
        if not len(s).bit_count() == 1:
            continue
        if all(x ^ y in s for x in s for y in s):
            groups[len(s).bit_length() - 1].add(s)
    return groups


def audit():
    representation = 0
    subspaces = 0
    for n in range(4):
        spaces = all_subspaces(n)
        for a in range(n + 1):
            seen = set()
            for _, subspace in injective_maps(a, n):
                representation += 1
                seen.add(subspace)
            assert seen == spaces[a], (n, a, len(seen), len(spaces[a]))
            subspaces += len(seen)
    compositions = 0
    for n in range(3):
        for m in range(n, 4):
            ambient_maps = list(injective_maps(n, m))
            for a in range(n + 1):
                for images, S in injective_maps(a, n):
                    for outer, _ in ambient_maps:
                        lhs = frozenset(apply(outer, s) for s in S)
                        composite_images = tuple(apply(outer, v) for v in images)
                        rhs = frozenset(apply(composite_images, x)
                                        for x in range(1 << a))
                        assert lhs == rhs
                        assert (lhs, frozenset({0})) == (rhs, frozenset({0}))
                        compositions += 1
    print('ONE-SIDED COPY/SUBSPACE FINITE REGRESSION: PASS')
    print(f'Injective source maps checked: {representation}')
    print(f'Distinct subspaces checked: {subspaces}')
    print(f'Nested embedding/composition pairs checked: {compositions}')
    print('Dimensions: all subspaces in F2^n for n <= 3; both one-sided sorts.')


if __name__ == '__main__':
    audit()
