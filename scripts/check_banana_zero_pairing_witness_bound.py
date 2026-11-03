#!/usr/bin/env python3
"""Finite adversarial check of sharp coherent-EPPA witness side dimension.

For the zero pairing on two sorts of dimensions l,r, embeddings into B_n
require orthogonal left/right subspaces. Exhaust all such subspaces for
n <= 3 and test the expected sharp inequality n >= l+r.
Not a Lean proof.
"""
from itertools import product


def span(vectors):
    values = {0}
    for v in vectors:
        values |= {w ^ v for w in tuple(values)}
    return frozenset(values)


def all_subspaces(n):
    spaces = {frozenset({0})}
    for v in range(1, 1 << n):
        spaces |= {span(s | {v}) for s in tuple(spaces)}
    return tuple(spaces)


def dot(x, y):
    return (x & y).bit_count() % 2


def dim(s):
    return len(s).bit_length() - 1


checks = 0
for n in range(4):
    spaces = all_subspaces(n)
    for l, r in product(range(4), repeat=2):
        if l > n or r > n:
            continue
        found = any(all(dot(x, y) == 0 for x in U for y in V)
                    for U in spaces if dim(U) == l
                    for V in spaces if dim(V) == r)
        assert found == (l + r <= n), (n, l, r, found)
        checks += 1

assert not any(all(dot(x, y) == 0 for x in U for y in V)
               for U in all_subspaces(1) if dim(U) == 1
               for V in all_subspaces(1) if dim(V) == 1)
assert any(all(dot(x, y) == 0 for x in U for y in V)
           for U in all_subspaces(2) if dim(U) == 1
           for V in all_subspaces(2) if dim(V) == 1)
print(f"Validated {checks} (ambient dimension, left dim, right dim) cases")
print("The side dimension l+r is sharp for the zero pairing")
