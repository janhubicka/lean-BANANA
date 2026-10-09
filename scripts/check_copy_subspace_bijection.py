#!/usr/bin/env python3
"""Finite regression for the one-sided BANANA copy/subspace equivalence.

For any ambient BANANA pairing, a one-sided source copy is an image
subspace on the nonzero sort and {0} on the zero sort. The ambient
pairing is deliberately arbitrary and irrelevant to the correspondence.
"""
from collections import Counter
from itertools import product


def apply_basis(basis, mask):
    z = 0
    for i, v in enumerate(basis):
        if mask & (1 << i):
            z ^= v
    return z


def injections(a, n):
    for basis in product(range(1 << n), repeat=a):
        images = frozenset(apply_basis(basis, x) for x in range(1 << a))
        if len(images) == 1 << a:
            yield basis, images


def subspaces(n, a):
    return {s for _, s in injections(a, n)}


def gl_size(a):
    out = 1
    for j in range(a):
        out *= (1 << a) - (1 << j)
    return out


def audit(n, a):
    reps = Counter(space for _, space in injections(a, n))
    expected = subspaces(n, a)
    assert set(reps) == expected
    assert all(v == gl_size(a) for v in reps.values())
    assert all(len(s) == 1 << a and 0 in s for s in expected)
    return len(reps), sum(reps.values())


def main():
    checks = embeddings = 0
    for n in range(5):
        dimensions = []
        for a in range(n + 1):
            count, reps = audit(n, a)
            dimensions.append(count)
            checks += count
            embeddings += reps
        print(f"PASS ambient dimension {n}: subspaces by rank = {dimensions}")
    naturality = 0
    for n in range(4):
        for m in range(n, 4):
            for ambient_basis, _ in injections(n, m):
                for a in range(n + 1):
                    for inner_basis, S in injections(a, n):
                        lhs = frozenset(apply_basis(ambient_basis, v) for v in S)
                        composite = tuple(apply_basis(ambient_basis, v) for v in inner_basis)
                        rhs = frozenset(apply_basis(composite, x) for x in range(1 << a))
                        assert lhs == rhs
                        assert len(rhs) == 1 << a
                        naturality += 1
    print(f"PASS {checks} subspaces, {embeddings} source embeddings, {naturality} composition checks")


if __name__ == "__main__":
    main()
