#!/usr/bin/env python3
"""Exhaustive tiny converse: finite ring embeddings are partial atom-owner maps.

Also checks that full pairing relation reflection is exactly equality of
the induced F2 atom matrix. Finite semantics only, not a Lean proof.
"""
from itertools import product

if not __debug__:
    raise SystemExit('Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.')


def pull(mask, owner):
    return sum(1 << j for j, a in enumerate(owner) if a >= 0 and (mask >> a) & 1)


def owners(n, m):
    return [o for o in product(range(-1, n), repeat=m)
            if all(a in o for a in range(n))]


def ring_embeddings(n, m):
    found = []
    for vals in product(range(1 << m), repeat=(1 << n) - 1):
        f = (0,) + vals
        if len(set(f)) != len(f):
            continue
        if all(f[x ^ y] == (f[x] ^ f[y]) and f[x & y] == (f[x] & f[y])
               for x in range(1 << n) for y in range(1 << n)):
            found.append(f)
    return found


def owner_from_map(f, n, m):
    own = []
    for j in range(m):
        names = [i for i in range(n) if (f[1 << i] >> j) & 1]
        assert len(names) <= 1  # disjointness of distinct source atoms
        own.append(names[0] if names else -1)
    assert all(a in own for a in range(n))
    assert tuple(pull(x, own) for x in range(1 << n)) == f
    return tuple(own)


def beta(mat, nr, x, y):
    return sum((mat >> (i * nr + j)) & 1
               for i in range(x.bit_length()) if (x >> i) & 1
               for j in range(y.bit_length()) if (y >> j) & 1) & 1


def induced(tmat, nr_target, ol, or_, nl, nr):
    return sum(beta(tmat, nr_target, pull(1 << i, ol), pull(1 << j, or_))
               << (i * nr + j)
               for i in range(nl) for j in range(nr))


def main():
    stats = dict(ring_maps=0, owner_maps=0, pairing_diagrams=0,
                 pairing_comparisons=0, zero_source_sorts=0,
                 maps_omitting_target_atoms=0)
    for n in range(3):
        for m in range(n, 4):
            actual = ring_embeddings(n, m)
            expected = {tuple(pull(x, o) for x in range(1 << n))
                        for o in owners(n, m)}
            assert set(actual) == expected
            assert len(actual) == len(expected)
            for f in actual:
                owner = owner_from_map(f, n, m)
                stats['maps_omitting_target_atoms'] += int(-1 in owner)
            stats['ring_maps'] += len(actual)
            stats['owner_maps'] += len(expected)
    for nl in range(2):
        for nr in range(2):
            for ml in range(nl, 3):
                for mr in range(nr, 3):
                    for fl in ring_embeddings(nl, ml):
                        for fr in ring_embeddings(nr, mr):
                            ol = owner_from_map(fl, nl, ml)
                            or_ = owner_from_map(fr, nr, mr)
                            for mat in range(1 << (ml * mr)):
                                src = induced(mat, mr, ol, or_, nl, nr)
                                for x in range(1 << nl):
                                    for y in range(1 << nr):
                                        assert beta(src, nr, x, y) == beta(mat, mr, fl[x], fr[y])
                                        stats['pairing_comparisons'] += 1
                                stats['pairing_diagrams'] += 1
                                stats['zero_source_sorts'] += int(nl == 0 or nr == 0)
    assert stats['ring_maps'] > 0 and stats['maps_omitting_target_atoms'] > 0
    assert stats['pairing_diagrams'] > 0 and stats['zero_source_sorts'] > 0
    print('PASS converse finite first-order/native embedding encoding (semantics only)')
    for name, value in stats.items():
        print(name + ':', value)


if __name__ == '__main__':
    main()
