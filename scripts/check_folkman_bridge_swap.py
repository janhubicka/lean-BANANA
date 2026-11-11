#!/usr/bin/env python3
"""Finite semantic adversary for swapping paired Folkman bridges.

Checks faithful partial-owner refinements in both copies, preservation
of full F2 pairings, and recovery of target-side back extensions by
source-side forth extensions of swapped bridges.

NOT Lean verification. No independently spawned referee.
"""
from itertools import permutations, product
from random import Random

if not __debug__:
    raise SystemExit("Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.")

rng = Random(20261111)

def image(mask, owner):
    return sum(1 << j for j, a in enumerate(owner) if a >= 0 and (mask >> a) & 1)

def permute(mask, p):
    return sum(1 << p[i] for i in range(len(p)) if (mask >> i) & 1)

def pair(bits, nr, x, y):
    return sum((bits >> (i * nr + j)) & 1 for i in range(x.bit_length())
               if (x >> i) & 1 for j in range(y.bit_length())
               if (x >> i) & 1 and (y >> j) & 1) % 2

def compress(owner):
    names = sorted(set(owner) - {-1})
    return tuple(names.index(v) if v >= 0 else -1 for v in owner)

def refine(owner):
    labels = [(a, rng.randrange(3)) if a >= 0 else
              (("private", j) if rng.randrange(2) else -1)
              for j, a in enumerate(owner)]
    keys = sorted(set(labels) - {-1}, key=str)
    return tuple(keys.index(v) if v != -1 else -1 for v in labels)

def link(old, new):
    n = max(new, default=-1) + 1
    result = []
    for j in range(n):
        values = {old[i] for i, k in enumerate(new) if k == j}
        assert len(values) == 1
        result.append(next(iter(values)))
    return tuple(result)

counts = dict(symmetries=0, commuting=0, pairing=0, back=0, zero=0, unused=0)
for nl in range(4):
    for nr in range(4):
        for bits in range(1 << (nl * nr)):
            for pl in permutations(range(nl)):
                for pr in permutations(range(nr)):
                    if any(pair(bits, nr, 1 << i, 1 << j) !=
                           pair(bits, nr, 1 << pl[i], 1 << pr[j])
                           for i in range(nl) for j in range(nr)):
                        continue
                    counts["symmetries"] += 1
                    ol = compress(tuple(rng.choice((-1, 0, 1, 2)) for _ in range(nl)))
                    or_ = compress(tuple(rng.choice((-1, 0, 1, 2)) for _ in range(nr)))
                    ql, qr = refine(ol), refine(or_)
                    fl, fr = link(ol, ql), link(or_, qr)
                    for owner, qowner, f, perm in ((ol, ql, fl, pl), (or_, qr, fr, pr)):
                        for x in range(1 << (max(owner, default=-1) + 1)):
                            a = image(x, owner)
                            b = permute(a, perm)
                            c = image(image(x, f), qowner)
                            d = permute(c, perm)
                            assert (a, b) == (c, d)
                            assert (b, a)[::-1] == (a, b)
                            counts["commuting"] += 2
                    for x in range(1 << (max(ol, default=-1) + 1)):
                        for y in range(1 << (max(or_, default=-1) + 1)):
                            sl, sr = image(x, ol), image(y, or_)
                            assert pair(bits, nr, sl, sr) == pair(
                                bits, nr, permute(sl, pl), permute(sr, pr))
                            counts["pairing"] += 1
                    for perm in (pl, pr):
                        inverse = tuple(perm.index(j) for j in range(len(perm)))
                        for x in range(1 << len(perm)):
                            assert permute(permute(x, inverse), perm) == x
                            counts["back"] += 1
                    counts["zero"] += int(not ol or not or_)
                    counts["unused"] += int(-1 in ol or -1 in or_)
assert counts["symmetries"] == 1717
assert counts["back"] > 0 and counts["unused"] > 0
print("PASS source/target bridge-swap semantics (NOT Lean kernel verification)")
print(counts)
