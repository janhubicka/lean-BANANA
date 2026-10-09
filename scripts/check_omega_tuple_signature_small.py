#!/usr/bin/env python3
"""Adversarial finite check of completeness of BANANA tuple signatures.

In the standard perfect binary pairing of dimensions 0..3, enumerate
all ordered tuples with at most two entries on each sort. Compare
equality of all coefficient dependencies and the cross-pairing table
with equivalence under GL(n,2), acting contragrediently on the right.

This is not a Lean proof and does not replace the general orbit theorem.
"""
from itertools import product


def dot(a, b):
    return (a & b).bit_count() & 1


def matmul(rows, x):
    return sum(dot(row, x) << i for i, row in enumerate(rows))


def xor_subset(xs, mask):
    out = 0
    for i, x in enumerate(xs):
        if mask >> i & 1:
            out ^= x
    return out


def signature(left, right):
    def relations(xs):
        return tuple(int(xor_subset(xs, c) == 0)
                     for c in range(1 << len(xs)))
    return (relations(left), relations(right),
            tuple(dot(x, y) for x in left for y in right))


def verify(n, l, r):
    vectors = range(1 << n)
    automorphisms = []
    for rows in product(vectors, repeat=n):
        table = [matmul(rows, x) for x in vectors]
        if len(set(table)) != (1 << n):
            continue
        # The right action is the inverse transpose.
        dual_rows = tuple(table.index(1 << i) for i in range(n))
        automorphisms.append((table, [matmul(dual_rows, y)
                                      for y in vectors]))
    cases = {}
    for left in product(vectors, repeat=l):
        for right in product(vectors, repeat=r):
            cases.setdefault(signature(left, right), set()).add((left, right))
    for key, bucket in cases.items():
        left, right = next(iter(bucket))
        orbit = {(tuple(f[x] for x in left), tuple(g[y] for y in right))
                 for f, g in automorphisms}
        if orbit != bucket:
            raise AssertionError(
                f"n={n}, l={l}, r={r}, signature={key}: "
                f"orbit={len(orbit)} but bucket={len(bucket)}"
            )
    return len(cases), len(automorphisms), sum(map(len, cases.values()))


def main():
    total_tuples = 0
    total_classes = 0
    for n in range(4):
        for l in range(3):
            for r in range(3):
                classes, group_size, tuples = verify(n, l, r)
                total_classes += classes
                total_tuples += tuples
                print(f"dimension={n} left={l} right={r}: "
                      f"{classes} classes, GL={group_size}, {tuples} tuples")
    assert (total_tuples, total_classes) == (5828, 277)
    print(f"OK: {total_tuples} tuples in {total_classes} "
          "orbit/signature classes")


if __name__ == "__main__":
    main()
