#!/usr/bin/env python3
"""Adversarial finite tests for non-unital Folkman term-value completeness.

Not a Lean kernel check. Covers zero rings, empty tuples, unused ambient
atoms, generated subrings and pairing reconstruction from finite profiles.
"""
from itertools import product
from random import Random


def blocks(n, xs):
    patterns = [sum(((x >> a) & 1) << i for i, x in enumerate(xs))
                for a in range(n)]
    return {p: sum(1 << a for a in range(n) if patterns[a] == p)
            for p in set(patterns) - {0}}


def closure(xs):
    out = set(xs) | {0}
    while True:
        new = out | {a ^ b for a in out for b in out} | \
              {a & b for a in out for b in out}
        if new == out:
            return out
        out = new


def canonical(n, xs):
    fs = blocks(n, xs)
    expected = {0}
    for mask in fs.values():
        expected |= {x | mask for x in tuple(expected)}
    assert closure(xs) == expected
    for i, x in enumerate(xs):
        assert x == sum(mask for p, mask in fs.items() if (p >> i) & 1)
    assert len(expected) == 1 << len(fs)
    return fs, expected


def pair(nl, nr, bits, x, y):
    return sum((bits >> (a * nr + b)) & 1 for a in range(nl)
               for b in range(nr) if (x >> a) & 1 and (y >> b) & 1) % 2


def profile(nl, nr, bits, xs, ys):
    l, _ = canonical(nl, xs)
    r, _ = canonical(nr, ys)
    return tuple(sorted(l)), tuple(sorted(r)), tuple(
        (p, q, pair(nl, nr, bits, l[p], r[q]))
        for p in sorted(l) for q in sorted(r))


def pairings_from_profile(nl, nr, bits, xs, ys):
    left, lring = canonical(nl, xs)
    right, rring = canonical(nr, ys)
    matrix = {(p, q): bit for p, q, bit in profile(nl, nr, bits, xs, ys)[2]}
    for x in lring:
        ps = [p for p, m in left.items() if x & m]
        for y in rring:
            qs = [q for q, m in right.items() if y & m]
            assert pair(nl, nr, bits, x, y) == sum(
                matrix[p, q] for p in ps for q in qs) % 2


def main():
    # Adversarial non-unitality witness: the empty tuple in the
    # two-element ambient ring generates only zero, *not* the ambient unit.
    assert canonical(1, ())[1] == {0}
    assert canonical(1, (0,))[1] == {0}
    assert canonical(0, ())[1] == {0}
    assert 1 not in canonical(1, ())[1]

    single = 0
    for n in range(4):
        for k in range(4):
            for xs in product(range(1 << n), repeat=k):
                canonical(n, xs)
                single += 1
    assert single == 689

    rng = Random(20261101)
    pairs = 0
    for nl in range(3):
        for nr in range(3):
            for bits in range(1 << (nl * nr)):
                for _ in range(70):
                    xs = tuple(rng.randrange(1 << nl)
                               for _ in range(rng.randrange(4)))
                    ys = tuple(rng.randrange(1 << nr)
                               for _ in range(rng.randrange(4)))
                    pairings_from_profile(nl, nr, bits, xs, ys)
                    pairs += 1
    for _ in range(7000):
        nl, nr = rng.randrange(7), rng.randrange(7)
        xs = tuple(rng.randrange(1 << nl) for _ in range(rng.randrange(5)))
        ys = tuple(rng.randrange(1 << nr) for _ in range(rng.randrange(5)))
        pairings_from_profile(nl, nr, rng.getrandbits(nl * nr), xs, ys)
        pairs += 1

    seen, collisions = {}, 0
    for _ in range(10000):
        nl, nr = rng.randrange(4), rng.randrange(4)
        xs = tuple(rng.randrange(1 << nl) for _ in range(2))
        ys = tuple(rng.randrange(1 << nr) for _ in range(2))
        bits = rng.getrandbits(nl * nr)
        key = profile(nl, nr, bits, xs, ys)
        if key in seen:
            collisions += 1
            ol, or_, ob, ox, oy = seen[key]
            l, lr = canonical(nl, xs)
            r, rr = canonical(nr, ys)
            l2, lr2 = canonical(ol, ox)
            r2, rr2 = canonical(or_, oy)
            for x in lr:
                xx = sum(m for p, m in l2.items() if x & l[p])
                assert xx in lr2
                for y in rr:
                    yy = sum(m for p, m in r2.items() if y & r[p])
                    assert yy in rr2
                    assert pair(nl, nr, bits, x, y) == pair(ol, or_, ob, xx, yy)
        else:
            seen[key] = nl, nr, bits, xs, ys
    print('generated-ring cases:', single)
    print('two-sort pairing cases:', pairs)
    print('profile-equivalent comparisons:', collisions)
    print('PASS (finite regression only; kernel verification pending)')


if __name__ == '__main__':
    main()
