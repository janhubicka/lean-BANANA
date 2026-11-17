#!/usr/bin/env python3
"""Exhaustively regress finite F2 bilinear pullback up to dimension two.

This is a finite calculation, NOT a Lean proof or substitute for a kernel build.
It includes rectangular and degenerate matrices, arbitrary (not necessarily
injective) linear maps, and zero-dimensional left/right sorts.
"""
from itertools import product


def matrices(rows, cols):
    for bits in product((0, 1), repeat=rows * cols):
        yield tuple(tuple(bits[i * cols + j] for j in range(cols)) for i in range(rows))


def vectors(n):
    return product((0, 1), repeat=n)


def image(M, ncols, v):
    return tuple(sum(M[i][j] * v[j] for j in range(ncols)) % 2 for i in range(len(M)))


def pairing(B, left, right):
    return sum(left[i] * B[i][j] * right[j]
               for i in range(len(left)) for j in range(len(right))) % 2


def pullback(B, fL, fR, aL, aR, bL, bR):
    return tuple(tuple(sum(fL[p][i] * B[p][q] * fR[q][j]
                           for p in range(bL) for q in range(bR)) % 2
                       for j in range(aR)) for i in range(aL))


def main():
    diagrams = pairs = zero_sort_diagrams = 0
    for aL, aR, bL, bR in product(range(3), repeat=4):
        for B in matrices(bL, bR):
            for fL in matrices(bL, aL):
                for fR in matrices(bR, aR):
                    diagrams += 1
                    zero_sort_diagrams += int(0 in (aL, aR, bL, bR))
                    PB = pullback(B, fL, fR, aL, aR, bL, bR)
                    for x in vectors(aL):
                        for y in vectors(aR):
                            pairs += 1
                            lhs = pairing(PB, x, y)
                            rhs = pairing(B, image(fL, aL, x), image(fR, aR, y))
                            if lhs != rhs:
                                raise AssertionError(
                                    (aL, aR, bL, bR, B, fL, fR, x, y, lhs, rhs)
                                )
    print(f"PASS: {diagrams:,} diagrams, {pairs:,} vector pairs, "
          f"{zero_sort_diagrams:,} diagrams with zero-dimensional sorts")


if __name__ == "__main__":
    main()
