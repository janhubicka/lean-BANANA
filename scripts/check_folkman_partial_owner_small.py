#!/usr/bin/env python3
"""Exhaustive finite non-unital Boolean-ring atom-owner classification.

A ring homomorphism between two finite powerset rings is determined
by the images of the source singleton atoms. This checks all such
images for source/target atom counts 0..4, including zero rings.
"""
from itertools import product


def image(basis, subset):
    out = 0
    for i, bits in enumerate(basis):
        if subset >> i & 1:
            out ^= bits
    return out


def main():
    total = ring = injective_ring = represented = nonunital = zero_source = 0
    for a in range(5):
        for b in range(5):
            for basis in product(range(1 << b), repeat=a):
                total += 1
                values = [image(basis, s) for s in range(1 << a)]
                preserves = all(
                    values[x ^ y] == (values[x] ^ values[y])
                    and values[x & y] == (values[x] & values[y])
                    for x in range(1 << a) for y in range(1 << a))
                injective = len(set(values)) == (1 << a)
                disjoint_nonzero = all(bits != 0 for bits in basis) and all(
                    basis[i] & basis[j] == 0 for i in range(a) for j in range(i))
                if preserves:
                    ring += 1
                if preserves and injective:
                    injective_ring += 1
                    assert disjoint_nonzero
                    owner = [next((i for i, bits in enumerate(basis)
                                   if bits >> j & 1), -1)
                             for j in range(b)]
                    assert all(i in owner for i in range(a))
                    assert all(
                        values[s] == sum(1 << j for j, i in enumerate(owner)
                                         if i != -1 and (s >> i & 1))
                        for s in range(1 << a))
                    represented += 1
                    if values[-1] != (1 << b) - 1:
                        nonunital += 1
                    if a == 0:
                        zero_source += 1
                else:
                    assert not disjoint_nonzero
    assert (total, ring, injective_ring, represented, nonunital, zero_source) == (
        74963, 1279, 185, 185, 92, 5)
    print(
        "Folkman partial-owner regression passed: 74963 finite maps; "
        "185 injective ring maps, all represented by partial owners; "
        "92 non-unital cases and all zero-ring sources covered.")


if __name__ == "__main__":
    main()
