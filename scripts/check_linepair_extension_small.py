#!/usr/bin/env python3
"""Exhaustive small-model regression for finite BANANA line-pair extension.

Not a Lean proof: verifies by enumeration that prescribed four-element
source embeddings extend through arbitrary two-sorted pairings into
standard perfect pairings for the dimensions listed in CASES.
"""
from itertools import product

CASES = [(1, 1, 0), (1, 1, 1), (1, 1, 2),
         (1, 2, 0), (2, 1, 0), (1, 2, 1), (2, 1, 1),
         (2, 2, 0), (1, 3, 0), (3, 1, 0)]


def parity(n):
    return n.bit_count() & 1


def images_of_basis(cols):
    out = [0]
    for col in cols:
        out += [x ^ col for x in out]
    return tuple(out)


def embeddings(n, d):
    for cols in product(range(1, 1 << n), repeat=d):
        out = images_of_basis(cols)
        if len(set(out)) == (1 << d):
            yield cols, out


def matrix_code(L, R, left_cols, right_cols):
    code = 0
    for i in range(L):
        for j in range(R):
            code |= parity(left_cols[i] & right_cols[j]) << (i * R + j)
    return code


def pairing(code, L, R, x, y):
    total = 0
    for i in range(L):
        if x & (1 << i):
            for j in range(R):
                if y & (1 << j):
                    total ^= (code >> (i * R + j)) & 1
    return total


def test_case(L, R, extra):
    n = L + R + extra
    mapsL = list(embeddings(n, L))
    mapsR = list(embeddings(n, R))
    seen = {}
    embeddings_examined = 0
    for left_cols, left_images in mapsL:
        for right_cols, right_images in mapsR:
            embeddings_examined += 1
            code = matrix_code(L, R, left_cols, right_cols)
            for x in range(1, 1 << L):
                for y in range(1, 1 << R):
                    key = (code, x, y)
                    seen.setdefault(key, set()).add((left_images[x], right_images[y]))

    target_pairs = {
        b: {(u, v) for u in range(1, 1 << n) for v in range(1, 1 << n)
            if parity(u & v) == b}
        for b in (0, 1)
    }
    assertions = 0
    for code in range(1 << (L * R)):
        for x in range(1, 1 << L):
            for y in range(1, 1 << R):
                expected = target_pairs[pairing(code, L, R, x, y)]
                actual = seen.get((code, x, y), set())
                assert actual == expected, (
                    f"FAIL L={L} R={R} extra={extra} code={code} "
                    f"x={x} y={y}: missing {sorted(expected - actual)[:4]}; "
                    f"unwanted {sorted(actual - expected)[:4]}"
                )
                assertions += 1
    return embeddings_examined, assertions


def main():
    pairs = 0
    assertions = 0
    for L, R, extra in CASES:
        checked, tests = test_case(L, R, extra)
        pairs += checked
        assertions += tests
        print(f"PASS L={L} R={R} extra={extra}: {checked} embedding pairs, "
              f"{tests} prescribed source-pair cases")
    print(f"PASS ALL {len(CASES)} CASES: {pairs} embedding pairs, "
          f"{assertions} coverage equalities")


if __name__ == '__main__':
    main()
