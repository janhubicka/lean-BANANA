#!/usr/bin/env python3
"""Exhaustive small-model check of unlabelled BANANA copy functoriality.

An ambient pairing on C pulls back along a pair of injective binary
linear maps B -> C. The image of a copy is its pair of subspaces.
Check (i) copy-range injectivity, (ii) exact line-pair palette pullback
for both pairing values, (iii) identity/composition for nested maps.
This is regression evidence, NOT Lean kernel verification.
"""
from itertools import product


def linear_image(columns, x):
    result = 0
    for i, v in enumerate(columns):
        if x & (1 << i):
            result ^= v
    return result


def injections(source_dim, target_dim):
    for columns in product(range(1 << target_dim), repeat=source_dim):
        vals = [linear_image(columns, x) for x in range(1 << source_dim)]
        if len(set(vals)) == (1 << source_dim):
            yield columns


def subspaces(n):
    answer = set()
    for a in range(n + 1):
        for f in injections(a, n):
            answer.add(frozenset(linear_image(f, x) for x in range(1 << a)))
    return tuple(sorted(answer, key=lambda s: (len(s), tuple(sorted(s)))))


def pairing(rows, x, y):
    t = 0
    for i, row in enumerate(rows):
        if x & (1 << i):
            t ^= row
    return (t & y).bit_count() & 1


def map_subspace(linear, subspace):
    return frozenset(linear_image(linear, v) for v in subspace)


def matrices(left, right):
    possible = 1 << (left * right)
    if possible <= 16:
        codes = range(possible)
    else:
        codes = set((0, 1, 2, 3, 5, 7, 21, 37, possible - 1))
    for code in codes:
        yield tuple((code >> (i * right)) & ((1 << right) - 1) for i in range(left))


def palette(ul, ur, rows, colour, b):
    return frozenset(colour(x, y) for x in ul if x for y in ur if y and pairing(rows, x, y) == b)


def check_functor():
    compared, checked_embeddings, unique_sets = 0, 0, 0
    for bl, br in product(range(3), repeat=2):
        small_c = range(bl, 4)
        large_c = range(br, 4)
        subs_l = subspaces(bl)
        subs_r = subspaces(br)
        source_copies = [(u, v) for u in subs_l for v in subs_r]
        for cl, cr in product(small_c, large_c):
            maps_l = list(injections(bl, cl))
            maps_r = list(injections(br, cr))
            ambient_matrices = list(matrices(cl, cr))
            for fl, fr in product(maps_l, maps_r):
                moved = [(map_subspace(fl, u), map_subspace(fr, v))
                         for u, v in source_copies]
                assert len(set(moved)) == len(source_copies), (bl, br, cl, cr)
                unique_sets += len(moved)
                for rows in ambient_matrices:
                    rows_b = tuple(sum(pairing(rows, linear_image(fl, 1 << i),
                                               linear_image(fr, 1 << j)) << j
                                       for j in range(br)) for i in range(bl))
                    for (u, v), (uf, vf) in zip(source_copies, moved):
                        for b in (0, 1):
                            # Two fixed ambient colouring functions: neither is
                            # invariant under a change of coordinates.
                            for colour in (
                                lambda x, y: (3*x + 5*y) % 7,
                                lambda x, y: (x ^ (y << 2)) % 11,
                            ):
                                in_target = palette(uf, vf, rows, colour, b)
                                pulled = palette(u, v, rows_b,
                                                 lambda x, y: colour(linear_image(fl, x),
                                                                     linear_image(fr, y)), b)
                                assert in_target == pulled, (bl, br, cl, cr, b)
                                compared += 1
                    checked_embeddings += 1
    return compared, checked_embeddings, unique_sets


def check_composition():
    total = 0
    # Nonzero and zero sorts are included. The two-step dimension increase
    # captures both pairing-positive and pairing-zero copy possibilities.
    for bl, br in product(range(2), repeat=2):
        for cl, cr in product(range(bl, 3), range(br, 3)):
            dl, dr = min(3, cl + 1), min(3, cr + 1)
            source_copies = [(u, v) for u in subspaces(bl) for v in subspaces(br)]
            for fl, fr, gl, gr in product(injections(bl, cl), injections(br, cr),
                                          injections(cl, dl), injections(cr, dr)):
                for u, v in source_copies:
                    left_1 = map_subspace(gl, map_subspace(fl, u))
                    right_1 = map_subspace(gr, map_subspace(fr, v))
                    left_2 = frozenset(linear_image(gl, linear_image(fl, x)) for x in u)
                    right_2 = frozenset(linear_image(gr, linear_image(fr, y)) for y in v)
                    assert (left_1, right_1) == (left_2, right_2)
                    total += 1
    return total


if __name__ == '__main__':
    comparisons, embeddings, copies = check_functor()
    compositions = check_composition()
    print('PASS exact palette pullback:', comparisons, 'comparisons')
    print('PASS injective copy-range maps:', copies, 'copy images across', embeddings, 'embedding/matrix cases')
    print('PASS functorial composition:', compositions, 'copy images')
