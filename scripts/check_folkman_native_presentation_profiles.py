#!/usr/bin/env python3
"""Finite semantic adversary for native Folkman profile transport.

Tests genuinely different ambient realisations and independent
atom enumerations, including unowned zero-pattern atoms. This
is NOT Lean kernel verification or an independent referee.
"""
from random import Random

rng = Random(20261106)


def bs(indices):
    return sum(1 << i for i in indices)


def blocks(patterns):
    return {p: bs(i for i, q in enumerate(patterns) if q == p)
            for p in sorted(set(patterns) - {0})}


def ring(block):
    values = {0}
    for f in block.values():
        values |= {x | f for x in tuple(values)}
    return values


def pairing(bits, nright, x, y):
    return sum((bits >> (i * nright + j)) & 1
               for i in range(x.bit_length()) if x & (1 << i)
               for j in range(y.bit_length()) if y & (1 << j)) % 2


def profile(left, right, bits):
    L, R = blocks(left), blocks(right)
    return (tuple(L), tuple(R),
            tuple(sorted((p, q, pairing(bits, len(right), x, y))
                         for p, x in L.items() for q, y in R.items())))


def realise(L, R, matrix):
    left = [p for p in L for _ in range(rng.randrange(1, 4))]
    right = [q for q in R for _ in range(rng.randrange(1, 4))]
    left += [0] * rng.randrange(4)
    right += [0] * rng.randrange(4)
    rng.shuffle(left)
    rng.shuffle(right)
    bits = rng.getrandbits(len(left) * len(right))
    lb, rb = blocks(left), blocks(right)
    for (p, q), wanted in matrix.items():
        i = left.index(p)
        j = right.index(q)
        correction = pairing(bits, len(right), lb[p], rb[q]) ^ wanted
        bits ^= correction << (i * len(right) + j)
    return tuple(left), tuple(right), bits


def transport(x, source, target):
    return bs(i for p, mask in target.items() if x & source[p]
              for i in range(mask.bit_length()) if mask & (1 << i))


def code(x, permutation):
    return bs(permutation[i] for i in range(len(permutation))
              if x & (1 << i))


def test_case(L, R, matrix):
    a = realise(L, R, matrix)
    b = realise(L, R, matrix)
    assert profile(*a) == profile(*b)
    leftA, rightA, pairA = a
    leftB, rightB, pairB = b
    LA, RA = blocks(leftA), blocks(rightA)
    LB, RB = blocks(leftB), blocks(rightB)
    Xa, Ya = ring(LA), ring(RA)
    Xb, Yb = ring(LB), ring(RB)
    f = {x: transport(x, LA, LB) for x in Xa}
    g = {y: transport(y, RA, RB) for y in Ya}
    assert len(set(f.values())) == len(Xb) and set(f.values()) == Xb
    assert len(set(g.values())) == len(Yb) and set(g.values()) == Yb
    for x in Xa:
        for z in Xa:
            assert f[x ^ z] == f[x] ^ f[z]
            assert f[x & z] == f[x] & f[z]
        for y in Ya:
            assert pairing(pairA, len(rightA), x, y) == pairing(
                pairB, len(rightB), f[x], g[y])
    for y in Ya:
        for z in Ya:
            assert g[y ^ z] == g[y] ^ g[z]
            assert g[y & z] == g[y] & g[z]
    for left, right, bits in (a, b):
        pl = list(range(len(left)))
        pr = list(range(len(right)))
        rng.shuffle(pl)
        rng.shuffle(pr)
        codeleft = tuple(left[pl.index(i)] for i in range(len(left)))
        coderight = tuple(right[pr.index(i)] for i in range(len(right)))
        codebits = 0
        for i in range(len(left)):
            for j in range(len(right)):
                codebits |= ((bits >> (i * len(right) + j)) & 1) << (
                    pl[i] * len(right) + pr[j])
        assert profile(left, right, bits) == profile(
            codeleft, coderight, codebits)
        for x in ring(blocks(left)):
            assert code(x, pl) in ring(blocks(codeleft))
            for y in ring(blocks(right)):
                assert pairing(bits, len(right), x, y) == pairing(
                    codebits, len(right), code(x, pl), code(y, pr))
    return len(Xa) * len(Ya)


def main():
    cases = pairing_checks = empty_sort = 0
    for nl in range(4):
        for nr in range(4):
            for _ in range(80):
                L = tuple(p for p in range(1, 1 << nl)
                          if rng.randrange(3) == 0)
                R = tuple(p for p in range(1, 1 << nr)
                          if rng.randrange(3) == 0)
                matrix = {(p, q): rng.randrange(2) for p in L for q in R}
                pairing_checks += test_case(L, R, matrix)
                cases += 1
                empty_sort += not L or not R
    assert cases == 1280 and empty_sort > 0
    # A matrix omitted from the profile would produce a false theorem.
    assert profile((1,), (1,), 0) != profile((1,), (1,), 1)
    # With no nonzero generator, the non-unital generated ring is zero.
    assert ring(blocks((0, 0, 0))) == {0}
    print("PASS finite native-presentation cases:", cases)
    print("PASS cases with an empty generated sort:", empty_sort)
    print("PASS full native pairing comparisons:", pairing_checks)
    print("NOT a Lean kernel check")


if __name__ == "__main__":
    main()
