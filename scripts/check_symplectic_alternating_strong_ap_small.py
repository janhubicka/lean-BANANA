#!/usr/bin/env python3
"""Independent finite adversarial check of strong coordinate amalgams of alternating F2 forms.

All alternating matrices with common subform are enumerated in small dimensions,
including zero- and odd-dimensional degenerate spaces.  Validate restriction,
vector-level pairing, injectivity, exact intersection of vector-space images,
and absence of spurious nondegeneracy assumptions.  Not a Lean proof.
"""
from itertools import product
from collections import Counter


def matrices(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        rows = [0] * n
        for idx, (i, j) in enumerate(pairs):
            if mask >> idx & 1:
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        yield tuple(rows)


def val(rows, x, y):
    out = 0
    for i, r in enumerate(rows):
        if x >> i & 1:
            out ^= (r & y).bit_count() & 1
    return out


def construct(B, C, a, x, y):
    n = a + x + y
    D = [0] * n
    for i in range(a + x):
        for j in range(a + x):
            D[i] |= ((B[i] >> j) & 1) << j
    for i in range(a + y):
        i2 = i if i < a else i + x
        for j in range(a + y):
            j2 = j if j < a else j + x
            # Common block values have already been checked equal.
            if i >= a or j >= a:
                D[i2] |= ((C[i] >> j) & 1) << j2
    return tuple(D)


def shift(v, a, x):
    return (v & ((1 << a) - 1)) | ((v >> a) << (a + x))


def check():
    counts = Counter()
    for a, x, y in product(range(3), repeat=3):
        msB = list(matrices(a + x))
        msC = list(matrices(a + y))
        # group by common A-block
        def key(m):
            return tuple(row & ((1 << a) - 1) for row in m[:a])
        buckets = {}
        for C in msC:
            buckets.setdefault(key(C), []).append(C)
        for B in msB:
            for C in buckets.get(key(B), []):
                D = construct(B, C, a, x, y)
                n = a + x + y
                assert all(not ((D[i] >> i) & 1) for i in range(n))
                assert all(((D[i] >> j) & 1) == ((D[j] >> i) & 1)
                           for i in range(n) for j in range(n))
                # first B is coordinate initial inclusion
                # second C has Y after the X summand
                imgB = set(range(1 << (a + x)))
                imgC = {shift(v, a, x) for v in range(1 << (a + y))}
                common = set(range(1 << a))
                assert imgB & imgC == common
                assert len(imgB) == 1 << (a + x)
                assert len(imgC) == 1 << (a + y)
                counts['amalgams'] += 1
                for u in range(1 << (a + x)):
                    for v in range(1 << (a + x)):
                        assert val(D, u, v) == val(B, u, v)
                        counts['left_pairing_checks'] += 1
                for u in range(1 << (a + y)):
                    for v in range(1 << (a + y)):
                        assert val(D, shift(u, a, x), shift(v, a, x)) == val(C, u, v)
                        counts['right_pairing_checks'] += 1
                for u in range(1 << (a + x)):
                    for v in range(1 << (a + y)):
                        is_equal = (u == shift(v, a, x))
                        is_common = (u < (1 << a) and v == u)
                        assert is_equal == is_common
                        counts['intersection_checks'] += 1
    print(dict(counts))
    assert counts['amalgams'] > 0
    print('PASS: all small alternating (possibly degenerate) block amalgams')

if __name__ == '__main__':
    check()
