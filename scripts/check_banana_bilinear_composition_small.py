#!/usr/bin/env python3
"""Adversarial F2 matrix-pullback composition regression.

Checks a standard identity twice: by exhaustive enumeration of every
three-stage diagram with six independent sort dimensions 0 or 1, and by
10,000 deterministic samples with dimensions 0, 1, 2 or 3.

This is a finite computation, not a Lean kernel proof.
"""
from itertools import product
import random


def matrices(rows, cols):
    for bits in product((0, 1), repeat=rows * cols):
        yield tuple(tuple(bits[i * cols + j] for j in range(cols))
                    for i in range(rows))


def compose(F, G, out_dim, mid_dim, in_dim):
    return tuple(tuple(
        sum(F[i][k] * G[k][j] for k in range(mid_dim)) % 2
        for j in range(in_dim)) for i in range(out_dim))


def pullback(B, L, R, source_left, source_right, target_left, target_right):
    return tuple(tuple(
        sum(L[p][i] * B[p][q] * R[q][j]
            for p in range(target_left) for q in range(target_right)) % 2
        for j in range(source_right)) for i in range(source_left))


def test_diagram(sL, sR, mL, mR, tL, tR, B, fL, fR, gL, gR):
    staged = pullback(
        pullback(B, fL, fR, mL, mR, tL, tR),
        gL, gR, sL, sR, mL, mR)
    cL = compose(fL, gL, tL, mL, sL)
    cR = compose(fR, gR, tR, mR, sR)
    combined = pullback(B, cL, cR, sL, sR, tL, tR)
    if staged != combined:
        raise AssertionError(
            (sL, sR, mL, mR, tL, tR, B, fL, fR, gL, gR,
             staged, combined))


def main():
    count = 0
    zero = 0
    for dims in product(range(2), repeat=6):
        sL, sR, mL, mR, tL, tR = dims
        for B in matrices(tL, tR):
            for fL in matrices(tL, mL):
                for fR in matrices(tR, mR):
                    for gL in matrices(mL, sL):
                        for gR in matrices(mR, sR):
                            test_diagram(*dims, B, fL, fR, gL, gR)
                            count += 1
                            zero += int(0 in dims)

    rng = random.Random(20261117)

    def rand_matrix(rows, cols):
        return tuple(tuple(rng.randrange(2) for _ in range(cols))
                     for _ in range(rows))

    random_count = 10000
    for _ in range(random_count):
        dims = tuple(rng.randrange(4) for _ in range(6))
        sL, sR, mL, mR, tL, tR = dims
        test_diagram(
            *dims, rand_matrix(tL, tR), rand_matrix(tL, mL),
            rand_matrix(tR, mR), rand_matrix(mL, sL),
            rand_matrix(mR, sR))
    print(
        f"PASS: {count:,} exhaustive three-stage diagrams (dimensions 0..1), "
        f"{random_count:,} seeded random diagrams (dimensions 0..3); "
        f"{zero:,} exhaustive cases with zero-dimensional sorts")


if __name__ == "__main__":
    main()
