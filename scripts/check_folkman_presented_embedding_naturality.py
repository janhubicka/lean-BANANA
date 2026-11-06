#!/usr/bin/env python3
"""Independent finite semantics for explicit native-to-atom owner compatibility.

No Lean code is executed here. This checks that the hypotheses for the
Track C native-presentation interface imply actual injectivity, exact
pairing preservation and invariance of the complete finite tuple profile.
"""
from itertools import product
from random import Random

rng = Random(20261106)


def owners(n, m):
    for seq in product(range(-1, n), repeat=m):
        if all(a in seq for a in range(n)):
            yield seq


def image(s, owner):
    return sum(1 << b for b, a in enumerate(owner)
               if a != -1 and ((s >> a) & 1))


def pairing(nl, nr, edge, x, y):
    return sum((edge >> (a * nr + b)) & 1
               for a in range(nl) for b in range(nr)
               if (x >> a) & 1 and (y >> b) & 1) % 2


def source_edges(nl, nr, ml, mr, edge, left_owner, right_owner):
    return sum(pairing(ml, mr, edge,
                       image(1 << a, left_owner),
                       image(1 << b, right_owner)) << (a * nr + b)
               for a in range(nl) for b in range(nr))


def profile(nl, nr, edge, xs, ys):
    left_signatures = [sum(((x >> a) & 1) << i for i, x in enumerate(xs))
                       for a in range(nl)]
    right_signatures = [sum(((y >> b) & 1) << j for j, y in enumerate(ys))
                        for b in range(nr)]
    left_patterns = frozenset(left_signatures) - {0}
    right_patterns = frozenset(right_signatures) - {0}
    pair_matrix = tuple((p, q,
                         sum((edge >> (a * nr + b)) & 1
                             for a, pa in enumerate(left_signatures)
                             for b, qb in enumerate(right_signatures)
                             if pa == p and qb == q) % 2)
                        for p in sorted(left_patterns)
                        for q in sorted(right_patterns))
    return (left_patterns, right_patterns, pair_matrix)


def verify_case(nl, nr, ml, mr, target_edge, lo, ro):
    s_edge = source_edges(nl, nr, ml, mr, target_edge, lo, ro)
    for x in range(1 << nl):
        xx = image(x, lo)
        assert xx.bit_count() >= x.bit_count()
        assert all(image(y, lo) != xx for y in range(1 << nl) if y != x)
        for z in range(1 << nl):
            assert image(x ^ z, lo) == xx ^ image(z, lo)
            assert image(x & z, lo) == xx & image(z, lo)
        for y in range(1 << nr):
            assert pairing(nl, nr, s_edge, x, y) == pairing(
                ml, mr, target_edge, xx, image(y, ro))
    for y in range(1 << nr):
        yy = image(y, ro)
        assert all(image(z, ro) != yy for z in range(1 << nr) if z != y)
        for z in range(1 << nr):
            assert image(y ^ z, ro) == yy ^ image(z, ro)
            assert image(y & z, ro) == yy & image(z, ro)
    checks = 0
    for _ in range(4):
        xs = tuple(rng.randrange(1 << nl) for _ in range(rng.randrange(4)))
        ys = tuple(rng.randrange(1 << nr) for _ in range(rng.randrange(4)))
        assert profile(nl, nr, s_edge, xs, ys) == profile(
            ml, mr, target_edge,
            tuple(image(x, lo) for x in xs),
            tuple(image(y, ro) for y in ys))
        checks += 1
    return checks


def main():
    configurations, profile_checks, empty_sorts = 0, 0, 0
    for nl in range(3):
        for nr in range(3):
            for ml in range(nl, 4):
                for mr in range(nr, 4):
                    ls = list(owners(nl, ml))
                    rs = list(owners(nr, mr))
                    for _ in range(10):
                        lo, ro = rng.choice(ls), rng.choice(rs)
                        target_edge = rng.getrandbits(ml * mr)
                        profile_checks += verify_case(
                            nl, nr, ml, mr, target_edge, lo, ro)
                        configurations += 1
                        empty_sorts += int(nl == 0 or nr == 0)
    # A bare atom-embedding existence claim forgets which native
    # homomorphism was specified: these valid left maps disagree.
    assert image(1, (0, -1)) != image(1, (0, 0))
    assert configurations == 810
    assert profile_checks == 3240
    assert empty_sorts > 0
    print('configured presented embeddings:', configurations)
    print('full tuple-profile equality checks:', profile_checks)
    print('configurations with a zero source sort:', empty_sorts)
    print('PASS; finite semantics, not Lean kernel verification')


if __name__ == '__main__':
    main()
