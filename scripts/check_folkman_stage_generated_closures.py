#!/usr/bin/env python3
"""Finite semantic adversary for generated non-unital ring closures.

A ring homomorphism of finite Boolean powerset rings is represented by a
partial owner map from target atoms to source atoms, with possibly empty
source fibres. This checker tests the exact image-of-closure identity,
finiteness, and (only for injective homomorphisms) the induced ring
isomorphism. It is NOT Lean kernel verification.
"""
from itertools import product
from random import Random
from collections import Counter

if not __debug__:
    raise SystemExit(
        "Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE."
    )


def closure(generators):
    elements = set(generators) | {0}
    while True:
        newer = elements | {a ^ b for a in elements for b in elements} | {
            a & b for a in elements for b in elements
        }
        if newer == elements:
            return elements
        elements = newer


def apply_owner(bits, owners):
    return sum(1 << j for j, a in enumerate(owners)
               if a >= 0 and bits & (1 << a))


def main():
    rng = Random(20261107)
    counts = Counter()
    for n in range(4):
        for m in range(5):
            all_owners = list(product(range(-1, n), repeat=m))
            chosen = (all_owners if len(all_owners) <= 90
                      else rng.sample(all_owners, 90))
            for owner in chosen:
                image = {apply_owner(x, owner) for x in range(1 << n)}
                injective = all(i in owner for i in range(n))
                if injective:
                    assert len(image) == (1 << n)
                for k in range(4):
                    tuples = list(product(range(1 << n), repeat=k))
                    if len(tuples) > 40:
                        tuples = rng.sample(tuples, 40)
                    for xs in tuples:
                        generated = closure(xs)
                        ys = tuple(apply_owner(x, owner) for x in xs)
                        image_generated = {apply_owner(x, owner)
                                           for x in generated}
                        target_generated = closure(ys)
                        assert image_generated == target_generated
                        assert target_generated <= image
                        if injective:
                            assert len(generated) == len(target_generated)
                            for a in generated:
                                for b in generated:
                                    assert apply_owner(a ^ b, owner) == (
                                        apply_owner(a, owner) ^
                                        apply_owner(b, owner))
                                    assert apply_owner(a & b, owner) == (
                                        apply_owner(a, owner) &
                                        apply_owner(b, owner))
                        counts['tuple_cases'] += 1
                        counts['injective_cases'] += injective
                        counts['noninjective_cases'] += not injective
                counts['owner_maps'] += 1
    # The injectivity hypothesis in the ring-equivalence theorem is
    # essential: a non-surjective owner can identify two source points.
    noninjective = (-1,)
    assert apply_owner(0, noninjective) == apply_owner(1, noninjective) == 0
    assert counts == {
        'tuple_cases': 23441,
        'injective_cases': 6895,
        'noninjective_cases': 16546,
        'owner_maps': 332,
    }
    print('finite partial-owner maps:', counts['owner_maps'])
    print('generated closure cases:', counts['tuple_cases'])
    print('injective transport cases:', counts['injective_cases'])
    print('non-injective transport cases:', counts['noninjective_cases'])
    print('PASS: non-unital closure image and injective isomorphism regressions')
    print('These are semantic tests, NOT Lean kernel checking.')


if __name__ == '__main__':
    main()
