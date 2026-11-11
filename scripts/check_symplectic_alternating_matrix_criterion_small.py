#!/usr/bin/env python3
"""Adversarial exhaustive F2 matrix criterion in dimensions 0..4.

A bilinear form x^T M y is alternating on ALL vectors precisely when
M is symmetric and has zero diagonal. Test every binary n x n matrix,
including degenerate and asymmetric examples. This is finite evidence,
NOT a Lean proof or an arbitrary-dimension certificate.
"""
from collections import Counter


def pairing(rows, x, y):
    v = 0
    for i, row in enumerate(rows):
        if (x >> i) & 1:
            v ^= (row & y).bit_count() & 1
    return v


def main():
    counts = Counter()
    for n in range(5):
        mask = (1 << n) - 1
        for code in range(1 << (n * n)):
            rows = tuple((code >> (i * n)) & mask for i in range(n))
            diag = all(((rows[i] >> i) & 1) == 0 for i in range(n))
            symm = all(((rows[i] >> j) & 1) == ((rows[j] >> i) & 1)
                       for i in range(n) for j in range(n))
            all_vectors = all(pairing(rows, x, x) == 0 for x in range(1 << n))
            assert all_vectors == (diag and symm), (n, rows)
            counts["matrices"] += 1
            counts["alternating_matrices"] += int(all_vectors)
    assert counts == {"matrices": 66067, "alternating_matrices": 76}
    for k, v in counts.items():
        print(f"{k}: {v:,}")
    print("PASS: zero diagonal AND symmetry iff alternation (n<=4)")


if __name__ == "__main__":
    main()
