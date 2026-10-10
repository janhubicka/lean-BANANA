#!/usr/bin/env python3
"""Exhaustive finite analogue of the mixed-sort BANANA tuple-orbit lemma.

For the perfect pairing on F₂^d, enumerate the full GL_d action on its
left sort and the contragredient action on its right sort. Confirm that
Boolean sort pattern, masked linear relations, and cross-pairings
classify every orbit of tagged tuples for the tested small dimensions.
This is a finite regression, not a proof of the countable limit theorem.
"""
from itertools import product


def image(cols, x):
    out = 0
    for i, v in enumerate(cols):
        if x & (1 << i):
            out ^= v
    return out


def pairing(x, y):
    return (x & y).bit_count() & 1


def automorphisms(dim):
    basis = tuple(1 << i for i in range(dim))
    for left in product(range(1 << dim), repeat=dim):
        if len({image(left, x) for x in range(1 << dim)}) != 1 << dim:
            continue
        right = tuple(next(y for y in range(1 << dim)
                           if all(pairing(image(left, e), y) == int(i == j)
                                  for i, e in enumerate(basis)))
                      for j in range(dim))
        for x, y in product(range(1 << dim), repeat=2):
            assert pairing(image(left, x), image(right, y)) == pairing(x, y)
        yield left, right


def signature(tagged):
    n = len(tagged)
    left = tuple(vec if sort == 0 else 0 for sort, vec in tagged)
    right = tuple(vec if sort == 1 else 0 for sort, vec in tagged)
    def relations(vectors):
        return tuple(int(image(vectors, bits) == 0) for bits in range(1 << n))
    return (tuple(sort for sort, _ in tagged),
            relations(left), relations(right),
            tuple(pairing(x, y) for x in left for y in right))


def act(tagged, left, right):
    return tuple((sort, image(left if sort == 0 else right, vec))
                 for sort, vec in tagged)


def check(dim, length):
    autos = tuple(automorphisms(dim))
    symbols = tuple(product((0, 1), range(1 << dim)))
    signatures = {}
    orbits = {}
    cases = 0
    for tagged in product(symbols, repeat=length):
        sig = signature(tagged)
        orbit = min(act(tagged, L, R) for L, R in autos)
        if sig in signatures:
            assert signatures[sig] == orbit, ('same signature, different orbit', dim, length, tagged)
        else:
            signatures[sig] = orbit
        if orbit in orbits:
            assert orbits[orbit] == sig, ('same orbit, different signature', dim, length, tagged)
        else:
            orbits[orbit] = sig
        cases += 1
    assert len(signatures) == len(orbits)
    print(f'PASS dimension={dim} tuple length={length}: '
          f'{cases} tagged tuples, {len(autos)} automorphisms, '
          f'{len(orbits)} exact signature/orbit classes')
    return cases


def main():
    total = 0
    for dim, max_length in [(0, 3), (1, 3), (2, 4), (3, 3)]:
        for length in range(max_length + 1):
            total += check(dim, length)
    print(f'PASS ALL {total} tagged tuples: signatures classify the exact finite GL-orbits')


if __name__ == '__main__':
    main()
