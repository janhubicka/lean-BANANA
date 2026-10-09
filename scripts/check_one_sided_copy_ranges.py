#!/usr/bin/env python3
"""One-sided BANANA copy/subspace correspondence: exhaustive finite regression.

A finite two-sorted BANANA structure consists of two binary vector spaces and
an arbitrary pairing. The pairing plays no role in copies with one zero sort.
Enumerate the injective linear maps, their image subspaces, and the induced
maps on unlabelled copies for all stated small ambient/source dimensions.
This is regression evidence, not a Lean proof.
"""
from itertools import product


def span(basis):
    images = (0,)
    for b in basis:
        images += tuple(x ^ b for x in images)
    return images


def injections(n, a):
    for basis in product(range(1, 1 << n), repeat=a):
        values = span(basis)
        if len(set(values)) == (1 << a):
            yield tuple(values)


def all_subspaces(n, a):
    return {frozenset(f) for f in injections(n, a)}


def induced_images(first, second):
    return frozenset(second[x] for x in first)


def check_case(nl, nr, bl, br):
    # For each ambient map B -> C (its induced bilinear form on B is the
    # pullback of C's form), check all one-sided source dimensions.
    lmaps = list(injections(nl, bl))
    rmaps = list(injections(nr, br))
    left_src = {a: list(injections(bl, a)) for a in range(bl + 1)}
    right_src = {a: list(injections(br, a)) for a in range(br + 1)}
    assert all({frozenset(i) for i in left_src[a]} == all_subspaces(bl, a)
               for a in left_src)
    assert all({frozenset(i) for i in right_src[a]} == all_subspaces(br, a)
               for a in right_src)
    checks = 0
    for fl in lmaps:
        for fr in rmaps:
            for a, maps in left_src.items():
                image_sets = {frozenset(m) for m in maps}
                assert len(image_sets) == len(all_subspaces(bl, a))
                for m in maps:
                    # Every representative of the same left subspace gives
                    # precisely the same image set in C; the empty right
                    # space is carried to the singleton {0}.
                    mapped = induced_images(m, fl)
                    assert mapped == frozenset(fl[x] for x in set(m))
                    assert len(mapped) == 1 << a
                    assert fr[0] == 0
                    checks += 1
            for a, maps in right_src.items():
                image_sets = {frozenset(m) for m in maps}
                assert len(image_sets) == len(all_subspaces(br, a))
                for m in maps:
                    mapped = induced_images(m, fr)
                    assert mapped == frozenset(fr[y] for y in set(m))
                    assert len(mapped) == 1 << a
                    assert fl[0] == 0
                    checks += 1
    return len(lmaps) * len(rmaps), checks


def main():
    total_maps = total_checks = 0
    cases = []
    for nl in range(0, 4):
        for nr in range(0, 4):
            for bl in range(min(nl, 2) + 1):
                for br in range(min(nr, 2) + 1):
                    cases.append((nl, nr, bl, br))
    for nl, nr, bl, br in cases:
        nmaps, checks = check_case(nl, nr, bl, br)
        total_maps += nmaps
        total_checks += checks
    print('PASS all %d dimension quadruples' % len(cases))
    print('PASS %d pairs of injective ambient sort maps' % total_maps)
    print('PASS %d one-sided copy/subspace and transport checks' % total_checks)
    for n in range(0, 5):
        print('Subspace counts F2^%d: %s' % (
            n, [len(all_subspaces(n, a)) for a in range(n + 1)]))


if __name__ == '__main__':
    main()
