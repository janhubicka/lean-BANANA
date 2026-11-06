#!/usr/bin/env python3
"""Independent adversarial regression for non-unital Folkman tuple profiles.

A source atom's membership pattern in a tuple is nonzero exactly when
it belongs to the generated non-unital subring. Under a non-unital
embedding (partial owner map, allowing unused target atoms), all
nonzero patterns and their induced matrix pairings must be preserved.

This finite regression does not replace a Lean theorem or kernel build.
"""
from collections import defaultdict
from itertools import product
from random import Random


def owners(n, m):
    for seq in product(range(-1, n), repeat=m):
        if all(i in seq for i in range(n)):
            yield seq


def image(x, owner):
    return sum(1 << i for i, atom in enumerate(owner)
               if atom >= 0 and (x >> atom) & 1)


def pairing(nl, nr, matrix, x, y):
    return sum((matrix >> (i * nr + j)) & 1
               for i in range(nl) for j in range(nr)
               if (x >> i) & 1 and (y >> j) & 1) % 2


def profile(nl, nr, matrix, xs, ys):
    pleft = [sum(((x >> i) & 1) << t for t, x in enumerate(xs))
             for i in range(nl)]
    pright = [sum(((y >> j) & 1) << t for t, y in enumerate(ys))
              for j in range(nr)]
    left = frozenset(pleft) - {0}
    right = frozenset(pright) - {0}
    out = {}
    for p in left:
        for q in right:
            out[p, q] = sum(
                (matrix >> (i * nr + j)) & 1
                for i in range(nl) for j in range(nr)
                if pleft[i] == p and pright[j] == q) % 2
    return left, right, tuple(sorted(out.items()))


def main():
    rng = Random(33117)
    configurations, profile_checks = 0, 0
    for nl in range(4):
        for nr in range(4):
            for ml in range(nl, 5):
                for mr in range(nr, 5):
                    left_maps = list(owners(nl, ml))
                    right_maps = list(owners(nr, mr))
                    if not left_maps or not right_maps:
                        continue
                    for _ in range(50):
                        fl = rng.choice(left_maps)
                        fr = rng.choice(right_maps)
                        ambient = rng.getrandbits(ml * mr)
                        source = 0
                        for i in range(nl):
                            for j in range(nr):
                                source |= pairing(
                                    ml, mr, ambient, image(1 << i, fl),
                                    image(1 << j, fr)) << (i * nr + j)
                        for _ in range(14):
                            xs = [rng.randrange(1 << nl)
                                  for _ in range(rng.randrange(5))]
                            ys = [rng.randrange(1 << nr)
                                  for _ in range(rng.randrange(5))]
                            assert profile(nl, nr, source, xs, ys) == profile(
                                ml, mr, ambient,
                                [image(x, fl) for x in xs],
                                [image(y, fr) for y in ys])
                            profile_checks += 1
                        configurations += 1
    assert configurations == 9800 and profile_checks == 137200
    print("embedding configurations:", configurations)
    print("tuple profile comparisons:", profile_checks)
    print("PASS; includes zero-ring sorts and unused target atoms")


if __name__ == "__main__":
    main()
