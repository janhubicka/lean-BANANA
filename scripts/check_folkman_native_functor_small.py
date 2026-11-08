#!/usr/bin/env python3
"""Independent finite adversarial check of the finite-index Folkman functor.

Exhaustively check identity, composition and the equivalence between
pairing preservation on all elements and its atom-matrix condition.
Non-unital embeddings are represented by partial atom-owner maps;
unowned target atoms and zero rings are included.
This is a finite regression, not a Lean proof.
"""
from collections import Counter
from itertools import product


def owners(n, m):
    for a in product(range(-1, n), repeat=m):
        if all(k in a for k in range(n)):
            yield a


def image(s, owner):
    return sum(1 << j for j, i in enumerate(owner)
               if i >= 0 and (s >> i) & 1)


def pairing(matrix, n_right, x, y):
    return sum((matrix >> (i * n_right + j)) & 1
               for i in range(x.bit_length()) for j in range(y.bit_length())
               if (x >> i) & 1 and (y >> j) & 1) % 2


def compose(f, g):
    # f: B-atoms -> A-atoms, g: C-atoms -> B-atoms
    return tuple(-1 if v < 0 else f[v] for v in g)


def main():
    stats = Counter()
    for a in range(4):
        for b in range(a, 4):
            for c in range(b, 4):
                for f in owners(a, b):
                    for g in owners(b, c):
                        h = compose(f, g)
                        assert all(k in h for k in range(a))
                        for x in range(1 << a):
                            assert image(x, h) == image(image(x, f), g)
                            stats["composition_checks"] += 1
    for n in range(4):
        id_owner = tuple(range(n))
        for x in range(1 << n):
            assert image(x, id_owner) == x
            stats["identity_checks"] += 1

    for sl in range(3):
        for sr in range(3):
            for tl in range(sl, 3):
                for tr in range(sr, 3):
                    for fl in owners(sl, tl):
                        for fr in owners(sr, tr):
                            for bmatrix in range(1 << (tl * tr)):
                                induced = sum(
                                    pairing(bmatrix, tr,
                                            image(1 << i, fl),
                                            image(1 << j, fr)) << (i * sr + j)
                                    for i in range(sl) for j in range(sr))
                                for amatrix in range(1 << (sl * sr)):
                                    atom_level = induced == amatrix
                                    all_elements = all(
                                        pairing(bmatrix, tr,
                                                image(x, fl), image(y, fr))
                                        == pairing(amatrix, sr, x, y)
                                        for x in range(1 << sl)
                                        for y in range(1 << sr))
                                    assert atom_level == all_elements
                                    stats["pairing_iff_configurations"] += 1

    assert stats == {
        "composition_checks": 913,
        "identity_checks": 15,
        "pairing_iff_configurations": 2451,
    }, stats
    for key, value in stats.items():
        print(f"{key}: {value:,}")
    print("PASS (finite regression only)")


if __name__ == "__main__":
    main()
