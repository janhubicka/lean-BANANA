#!/usr/bin/env python3
"""Exhaustive small-dimensional regression for the arbitrary BANANA amalgam.

For finite F2 pairings A -> B and A -> C, use linear retractions to
embed B and C into A ⊕ B ⊕ C. Verify pairing preservation, agreement
over A and strong intersection separately on the two sorts.
This tests finite models; it does not prove the Lean statement.
"""
from itertools import product


def lin(columns, x):
    z = 0
    for i, c in enumerate(columns):
        if x & (1 << i):
            z ^= c
    return z


def embeddings(a, b):
    for columns in product(range(1 << b), repeat=a):
        if len({lin(columns, x) for x in range(1 << a)}) == 1 << a:
            yield columns


def retract(f, a, b):
    for columns in product(range(1 << a), repeat=b):
        if all(lin(columns, lin(f, 1 << i)) == 1 << i for i in range(a)):
            return columns
    raise AssertionError("An injective linear map lacks a left inverse")


def pairing(rows, x, y):
    z = 0
    for i, row in enumerate(rows):
        if x & (1 << i):
            z ^= row
    return (z & y).bit_count() & 1


def matrix(code, a, b):
    return tuple((code >> (i * b)) & ((1 << b) - 1) for i in range(a))


def restriction(rows, fL, fR, aL, aR):
    return tuple(
        sum(pairing(rows, lin(fL, 1 << i), lin(fR, 1 << j)) << j
            for j in range(aR))
        for i in range(aL)
    )


def test_dimensions(aL, aR, bL, bR, cL, cR):
    mapsBL = list(embeddings(aL, bL))
    mapsBR = list(embeddings(aR, bR))
    mapsCL = list(embeddings(aL, cL))
    mapsCR = list(embeddings(aR, cR))
    by_common = {}
    for Bcode in range(1 << (bL * bR)):
        Bmat = matrix(Bcode, bL, bR)
        for fL, fR in product(mapsBL, mapsBR):
            A = restriction(Bmat, fL, fR, aL, aR)
            by_common.setdefault(A, []).append((Bmat, fL, fR))
    total = 0
    for Ccode in range(1 << (cL * cR)):
        Cmat = matrix(Ccode, cL, cR)
        for gL, gR in product(mapsCL, mapsCR):
            A = restriction(Cmat, gL, gR, aL, aR)
            for Bmat, fL, fR in by_common.get(A, []):
                pBL = retract(fL, aL, bL)
                pBR = retract(fR, aR, bR)
                pCL = retract(gL, aL, cL)
                pCR = retract(gR, aR, cR)

                def leftB(b):
                    a = lin(pBL, b)
                    return a, b ^ lin(fL, a), 0

                def rightB(y):
                    a = lin(pBR, y)
                    return a, y ^ lin(fR, a), 0

                def leftC(c):
                    a = lin(pCL, c)
                    return a, 0, c ^ lin(gL, a)

                def rightC(y):
                    a = lin(pCR, y)
                    return a, 0, y ^ lin(gR, a)

                def betaD(x, y):
                    a, u, v = x
                    z, s, t = y
                    return (
                        pairing(Bmat, lin(fL, a) ^ u, lin(fR, z) ^ s)
                        ^ pairing(Cmat, lin(gL, a) ^ v, lin(gR, z) ^ t)
                        ^ pairing(A, a, z)
                    )

                for x, y in product(range(1 << bL), range(1 << bR)):
                    assert betaD(leftB(x), rightB(y)) == pairing(Bmat, x, y)
                for x, y in product(range(1 << cL), range(1 << cR)):
                    assert betaD(leftC(x), rightC(y)) == pairing(Cmat, x, y)
                for x, y in product(range(1 << bL), range(1 << cL)):
                    assert (leftB(x) == leftC(y)) == any(
                        x == lin(fL, a) and y == lin(gL, a)
                        for a in range(1 << aL)
                    )
                for x, y in product(range(1 << bR), range(1 << cR)):
                    assert (rightB(x) == rightC(y)) == any(
                        x == lin(fR, a) and y == lin(gR, a)
                        for a in range(1 << aR)
                    )
                for a in range(1 << aL):
                    assert leftB(lin(fL, a)) == leftC(lin(gL, a))
                for a in range(1 << aR):
                    assert rightB(lin(fR, a)) == rightC(lin(gR, a))
                total += 1
    return total


if __name__ == "__main__":
    cases = [(0, 0, 2, 2, 2, 2), (1, 0, 2, 2, 2, 2),
             (0, 1, 2, 2, 2, 2), (1, 1, 2, 2, 2, 2)]
    totals = [test_dimensions(*case) for case in cases]
    for case, number in zip(cases, totals):
        print("PASS", case, "diagrams:", number)
    assert totals == [256, 2304, 2304, 10368]
    print("PASS TOTAL strong amalgamation diagrams:", sum(totals))
