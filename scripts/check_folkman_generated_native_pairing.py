#!/usr/bin/env python3
"""Finite native Folkman pairing on generated subrings (semantic only)."""
from itertools import product
from random import Random

if not __debug__:
    raise SystemExit("Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.")

rng = Random(20261108)

def f(mask, owner):
    return sum(1 << j for j, i in enumerate(owner) if i >= 0 and mask & (1 << i))

def beta(matrix, nR, x, y):
    return sum((matrix >> (i * nR + j)) & 1
               for i in range(x.bit_length()) if x & (1 << i)
               for j in range(y.bit_length()) if y & (1 << j)) % 2

def closure(gens):
    seen = set(gens) | {0}
    while True:
        nxt = seen | {a ^ b for a in seen for b in seen}
        nxt |= {a & b for a in seen for b in seen}
        if nxt == seen:
            return seen
        seen = nxt

def owners(n, m):
    return [o for o in product(range(-1, n), repeat=m)
            if all(i in o for i in range(n))]

def main():
    counts = dict(cases=0, pairing_checks=0, generated_zero_sorts=0,
                  unowned_target_atoms=0)
    for nl in range(4):
        for nr in range(4):
            for ml in range(nl, 5):
                for mr in range(nr, 5):
                    ll, rr = owners(nl, ml), owners(nr, mr)
                    for _ in range(15):
                        ol, or_ = rng.choice(ll), rng.choice(rr)
                        matrix = rng.getrandbits(ml * mr)
                        xg = tuple(rng.randrange(1 << nl)
                                   for _ in range(rng.randrange(4)))
                        yg = tuple(rng.randrange(1 << nr)
                                   for _ in range(rng.randrange(4)))
                        X = closure(f(x, ol) for x in xg)
                        Y = closure(f(y, or_) for y in yg)
                        ux, uy = 0, 0
                        for x in X:
                            ux |= x
                        for y in Y:
                            uy |= y
                        assert all((ux & x) == x for x in X)
                        assert all((uy & y) == y for y in Y)
                        assert ux in X and uy in Y
                        counts["generated_zero_sorts"] += int(X == {0} or Y == {0})
                        counts["unowned_target_atoms"] += int(-1 in ol or -1 in or_)
                        for x in X:
                            for xp in X:
                                for y in Y:
                                    assert beta(matrix, mr, x ^ xp, y) == (
                                        beta(matrix, mr, x, y) ^
                                        beta(matrix, mr, xp, y))
                                    counts["pairing_checks"] += 1
                        for y in Y:
                            for yp in Y:
                                for x in X:
                                    assert beta(matrix, mr, x, y ^ yp) == (
                                        beta(matrix, mr, x, y) ^
                                        beta(matrix, mr, x, yp))
                                    counts["pairing_checks"] += 1
                        counts["cases"] += 1
    assert counts == dict(cases=2940, pairing_checks=46366,
                          generated_zero_sorts=2497, unowned_target_atoms=2382)
    print("PASS generated native pairing, finite semantics only")
    for key, value in counts.items():
        print(key, value)

if __name__ == "__main__":
    main()
