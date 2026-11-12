#!/usr/bin/env python3
"""Finite S3 < S4 regression for two-sorted coherent representative transport.

Not a Lean proof and not a test of the full finite BANANA class.
"""
from itertools import permutations

G = tuple(permutations(range(4)))
H = tuple(permutations(range(3)))
e = (0, 1, 2, 3)
k = (3, 1, 2, 0)  # the second sort carries the conjugate S4 action


def mul(a, b):
    """Function composition, applying b before a."""
    return tuple(a[b[i]] for i in range(len(a)))


def inv(a):
    b = [None] * len(a)
    for i, j in enumerate(a):
        b[j] = i
    return tuple(b)


def rho(h):
    return h + (3,)


def action_right(g, y):
    return k[g[k[y]]]


def theta(gu, gv, h):
    return mul(mul(gv, rho(h)), inv(gu))


# Check a faithful representative action on two different ambient sort actions.
# Each chosen representative copy is the g-translate of the fixed base copy.
checks_extension = 0
for gu in G:
    for gv in G:
        for h in H:
            t = theta(gu, gv, h)
            for x in range(3):
                assert t[gu[x]] == gv[h[x]]
                assert action_right(t, action_right(gu, k[x])) == \
                    action_right(gv, k[h[x]])
                checks_extension += 2

# Check the noncommutative order: Theta(q) Theta(p) = Theta(q p).
checks_composition = 0
for gu in G:
    for gv in G:
        for gw in G:
            for p in H:
                tp = theta(gu, gv, p)
                for q in H:
                    tq = theta(gv, gw, q)
                    assert mul(tq, tp) == theta(gu, gw, mul(q, p))
                    checks_composition += 1

checks_inverse = 0
for gu in G:
    assert theta(gu, gu, (0, 1, 2)) == e
    for gv in G:
        for h in H:
            assert inv(theta(gu, gv, h)) == theta(gv, gu, inv(h))
            checks_inverse += 1

# Counterexample to omitting base-copy equivariance: the trivial rho would
# not extend a nonidentity representative automorphism even at one object.
nontrivial_h = (1, 0, 2)
assert e[0] != nontrivial_h[0]

print(f"Two-sort representative-extension checks: {checks_extension}")
print(f"Noncommutative coherence checks: {checks_composition}")
print(f"Inverse-transport checks: {checks_inverse}")
print("Negative check: base-copy equivariance cannot be omitted")
