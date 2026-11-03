#!/usr/bin/env python3
"""Exhaustive finite adversarial check of adapted F2-vector-space coordinates.

For ALL injective linear maps F2^a -> F2^b with 0<=a<=b<=3,
and ALL invertible choices of source coordinates, construct an
ordinary (not orthogonal) complement basis of the target.
Check the coordinate identity eB(i(x))=(eA(x),0) on ALL source vectors,
and verify that the completed target basis is invertible.

Finite regression only: not a Lean kernel verification.
"""
from collections import Counter
from itertools import product


def apply(cols, v):
    out = 0
    for i, c in enumerate(cols):
        if (v >> i) & 1:
            out ^= c
    return out


def rank(cols):
    seen = {0}
    for c in cols:
        more = {w ^ c for w in seen}
        if more & seen:
            return len(seen).bit_length() - 1
        seen |= more
    return len(cols)


def bases(n):
    for cols in product(range(1 << n), repeat=n):
        if rank(cols) == n:
            yield cols


def injections(a, b):
    for cols in product(range(1 << b), repeat=a):
        if rank(cols) == a:
            yield cols


def inverse(cols):
    n = len(cols)
    table = {apply(cols, v): v for v in range(1 << n)}
    assert len(table) == 1 << n
    return tuple(table[1 << i] for i in range(n))


def extend_basis(cols, dimension):
    out = list(cols)
    for c in range(1 << dimension):
        if len(out) == dimension:
            break
        if rank(out + [c]) == len(out) + 1:
            out.append(c)
    assert len(out) == dimension and rank(out) == dimension
    return tuple(out)


def main():
    stats = Counter()
    for a in range(4):
        for b in range(a, 4):
            for injection in injections(a, b):
                for source_coordinates in bases(a):
                    source_basis = inverse(source_coordinates)
                    common_columns = [
                        apply(injection, source_basis[i]) for i in range(a)
                    ]
                    target_basis = extend_basis(common_columns, b)
                    target_coordinates = inverse(target_basis)
                    for x in range(1 << a):
                        assert apply(
                            target_coordinates, apply(injection, x)
                        ) == apply(source_coordinates, x)
                        stats["coordinate_identity_checks"] += 1
                    stats["adapted_basis_choices"] += 1
    assert stats == {
        "coordinate_identity_checks": 226970,
        "adapted_basis_choices": 28527,
    }, stats
    for key, count in stats.items():
        print(f"{key}: {count:,}")
    print("PASS: all small injective maps and source coordinates")


if __name__ == "__main__":
    main()
