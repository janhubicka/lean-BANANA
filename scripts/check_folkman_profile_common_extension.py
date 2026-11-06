#!/usr/bin/env python3
"""Adversarial finite semantics: two compatible embeddings into a common stage.

Confirms that equal labelled tuples in a common finite target produce the
same complete two-sort profile in both source presentations.
Not a Lean kernel check or independent referee certification.
"""
from random import Random
from check_folkman_presented_embedding_naturality import (
    owners, image, profile, source_edges,
)

rng = Random(20261106)


def choose_owner(n, m):
    return rng.choice(tuple(owners(n, m)))


def common_tuple(n_a, n_b, m, e, f):
    aa = {image(x, e): x for x in range(1 << n_a)}
    bb = {image(x, f): x for x in range(1 << n_b)}
    common = tuple(sorted(set(aa) & set(bb)))
    assert 0 in common
    vals = [rng.choice(common) for _ in range(rng.randrange(4))]
    return tuple(aa[s] for s in vals), tuple(bb[s] for s in vals)


def main():
    trials = comparisons = nonzero = empty = 0
    for ml in range(4):
        for mr in range(4):
            for _ in range(100):
                al, bl = rng.randrange(ml + 1), rng.randrange(ml + 1)
                ar, br = rng.randrange(mr + 1), rng.randrange(mr + 1)
                el, fl = choose_owner(al, ml), choose_owner(bl, ml)
                er, fr = choose_owner(ar, mr), choose_owner(br, mr)
                edge = rng.getrandbits(ml * mr)
                a_edge = source_edges(al, ar, ml, mr, edge, el, er)
                b_edge = source_edges(bl, br, ml, mr, edge, fl, fr)
                for _ in range(8):
                    xs_a, xs_b = common_tuple(al, bl, ml, el, fl)
                    ys_a, ys_b = common_tuple(ar, br, mr, er, fr)
                    assert tuple(map(lambda s: image(s, el), xs_a)) == tuple(
                        map(lambda s: image(s, fl), xs_b))
                    assert tuple(map(lambda s: image(s, er), ys_a)) == tuple(
                        map(lambda s: image(s, fr), ys_b))
                    assert profile(al, ar, a_edge, xs_a, ys_a) == profile(
                        bl, br, b_edge, xs_b, ys_b)
                    comparisons += 1
                    nonzero += any(xs_a) or any(ys_a)
                trials += 1
                empty += (al == 0 or ar == 0 or bl == 0 or br == 0)
    assert trials == 1600
    assert comparisons == 12800
    assert nonzero > 0
    assert empty > 0
    print('common-extension configurations:', trials)
    print('complete source-profile comparisons:', comparisons)
    print('comparisons with nonzero named elements:', nonzero)
    print('configurations containing a zero source sort:', empty)
    print('PASS; finite semantics only, not a Lean kernel check')


if __name__ == '__main__':
    main()
