#!/usr/bin/env python3
"""Independent finite test: arbitrary linear coordinates in alternating F2 amalgams.

Each source space undergoes a random invertible change of basis, moving the
common subspace away from its standard coordinate position. Verify full
bilinear preservation and exact strong intersection in the transported
amalgam. Includes zero, degenerate and odd-dimensional forms.
This is not a kernel proof or an exhaustive theorem in all dimensions.
"""
from itertools import product
from collections import Counter
from random import Random


def image(cols, x):
    ans = 0
    for i, c in enumerate(cols):
        if x >> i & 1:
            ans ^= c
    return ans


def change_of_basis(n, rng):
    cols = [1 << i for i in range(n)]
    for _ in range(9 * n):
        if n < 2:
            break
        i = rng.randrange(n)
        j = rng.randrange(n - 1)
        if j >= i:
            j += 1
        if rng.randrange(2):
            cols[i], cols[j] = cols[j], cols[i]
        else:
            cols[i] ^= cols[j]
    assert {image(cols, x) for x in range(1 << n)} == set(range(1 << n))
    inv = [next(x for x in range(1 << n) if image(cols, x) == 1 << i)
           for i in range(n)]
    return cols, inv


def alternating(n, rng):
    rows = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if rng.randrange(2):
                rows[i] |= 1 << j
                rows[j] |= 1 << i
    return tuple(rows)


def pairing(rows, x, y):
    return sum((r & y).bit_count() for i, r in enumerate(rows)
               if x >> i & 1) & 1


def block_amalgam(B, C, a, x, y):
    D = [0] * (a + x + y)
    for i in range(a + x):
        for j in range(a + x):
            D[i] |= ((B[i] >> j) & 1) << j
    for i in range(a + y):
        ii = i if i < a else i + x
        for j in range(a + y):
            jj = j if j < a else j + x
            if i >= a or j >= a:
                D[ii] |= ((C[i] >> j) & 1) << jj
    return tuple(D)


def include_right(z, a, x):
    return (z & ((1 << a) - 1)) | ((z >> a) << (a + x))


def main():
    rng = Random(20261102)
    tests = Counter()
    for a, x, y in product(range(3), repeat=3):
        nb, nc, nd = a + x, a + y, a + x + y
        for _ in range(53):
            B = alternating(nb, rng)
            C = list(alternating(nc, rng))
            for i in range(a):
                for j in range(a):
                    if B[i] >> j & 1:
                        C[i] |= 1 << j
                    else:
                        C[i] &= ~(1 << j)
            C = tuple(C)
            D = block_amalgam(B, C, a, x, y)
            assert all(pairing(D, z, z) == 0 for z in range(1 << nd))
            TB, IB = change_of_basis(nb, rng)
            TC, IC = change_of_basis(nc, rng)
            fB = lambda u: image(IB, u)
            fC = lambda v: include_right(image(IC, v), a, x)
            for z in range(1 << a):
                assert fB(image(TB, z)) == z
                assert fC(image(TC, z)) == z
                tests["common_embedding"] += 1
            for u in range(1 << nb):
                for v in range(1 << nb):
                    assert pairing(B, image(IB, u), image(IB, v)) == pairing(
                        D, fB(u), fB(v))
                    tests["left_pairing"] += 1
            for u in range(1 << nc):
                for v in range(1 << nc):
                    assert pairing(C, image(IC, u), image(IC, v)) == pairing(
                        D, fC(u), fC(v))
                    tests["right_pairing"] += 1
            for u in range(1 << nb):
                for v in range(1 << nc):
                    equal = fB(u) == fC(v)
                    common = any(image(TB, z) == u and image(TC, z) == v
                                 for z in range(1 << a))
                    assert equal == common
                    tests["strong_intersection"] += 1
            tests["amalgams"] += 1
    assert tests == dict(common_embedding=3339, left_pairing=70119,
                         right_pairing=70119, strong_intersection=54537,
                         amalgams=1431), tests
    for name, count in tests.items():
        print(f"{name}: {count:,}")
    print("PASS: non-coordinate common images and arbitrary change of basis")


if __name__ == "__main__":
    main()
