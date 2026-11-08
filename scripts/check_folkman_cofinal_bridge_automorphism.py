#!/usr/bin/env python3
"""Finite two-sort cofinal-bridge endpoint regression.

A constant chain whose code is the entire finite ambient Boolean ring
and whose target embedding is an atom permutation provides an explicit
exhaustive coherent bridge. Its global map must preserve the pairing
exactly when the matrix is invariant under the two permutations.

Tests finite semantics, NOT the Lean proof.
"""
from itertools import permutations

if not __debug__:
    raise SystemExit("Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.")


def permute(mask, perm):
    return sum(1 << perm[i] for i in range(len(perm)) if mask & (1 << i))


def pairing(bits, nr, x, y):
    return sum((bits >> (i * nr + j)) & 1 for i in range(x.bit_length())
               if (x >> i) & 1 for j in range(y.bit_length()) if (y >> j) & 1) % 2


def test():
    total, allowed, rejected, pairing_checks, operation_checks = 0, 0, 0, 0, 0
    for nl in range(4):
        for nr in range(4):
            for bits in range(1 << (nl * nr)):
                for pl in permutations(range(nl)):
                    for pr in permutations(range(nr)):
                        total += 1
                        singleton_ok = all(
                            pairing(bits, nr, 1 << i, 1 << j) ==
                            pairing(bits, nr, 1 << pl[i], 1 << pr[j])
                            for i in range(nl) for j in range(nr))
                        full_ok = True
                        for x in range(1 << nl):
                            mx = permute(x, pl)
                            for u in range(1 << nl):
                                assert permute(x ^ u, pl) == mx ^ permute(u, pl)
                                assert permute(x & u, pl) == mx & permute(u, pl)
                                operation_checks += 2
                            for y in range(1 << nr):
                                my = permute(y, pr)
                                result = (pairing(bits, nr, x, y) ==
                                          pairing(bits, nr, mx, my))
                                full_ok &= result
                                pairing_checks += 1
                        assert full_ok == singleton_ok
                        if full_ok:
                            allowed += 1
                        else:
                            rejected += 1
                        for y in range(1 << nr):
                            my = permute(y, pr)
                            for v in range(1 << nr):
                                assert permute(y ^ v, pr) == my ^ permute(v, pr)
                                assert permute(y & v, pr) == my & permute(v, pr)
                                operation_checks += 2
    assert total == allowed + rejected
    assert allowed > 0 and rejected > 0
    print("all finite full-code bridges tested:", total)
    print("admissible pairing-preserving bridges:", allowed)
    print("inadmissible non-pairing bridges rejected:", rejected)
    print("pairing checks:", pairing_checks)
    print("operation checks:", operation_checks)
    print("PASS: finite semantic regression, not Lean kernel certification")


if __name__ == "__main__":
    test()
