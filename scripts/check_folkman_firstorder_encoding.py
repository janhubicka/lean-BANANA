#!/usr/bin/env python3
"""Finite adversarial test of a tagged single-sorted Folkman encoding.

The signatures have two zero constants, four totalised binary ring
operations, two unary sort predicates and a binary pairing-one relation.
All tests are finite semantics, NOT Lean kernel verification.
"""
from itertools import product
from random import Random

if not __debug__:
    raise SystemExit('Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.')

rng = Random(20261111)


def owner_maps(n, m):
    return [o for o in product(range(-1, n), repeat=m)
            if all(i in o for i in range(n))]


def pull(mask, owner):
    return sum(1 << j for j, i in enumerate(owner)
               if i >= 0 and ((mask >> i) & 1))


def beta(matrix, right_atoms, left, right):
    return sum((matrix >> (i * right_atoms + j)) & 1
               for i in range(left.bit_length()) if (left >> i) & 1
               for j in range(right.bit_length()) if (right >> j) & 1) % 2


def induced_matrix(bits, nr_target, ol, or_, nl_source, nr_source):
    return sum(beta(bits, nr_target, pull(1 << i, ol), pull(1 << j, or_))
               << (i * nr_source + j)
               for i in range(nl_source) for j in range(nr_source))


def elems(nl, nr):
    return [('L', x) for x in range(1 << nl)] + [('R', y) for y in range(1 << nr)]


def op(symbol, v, w):
    sort, kind = symbol
    if v[0] != sort or w[0] != sort:
        return sort, 0
    return sort, (v[1] ^ w[1] if kind == '+' else v[1] & w[1])


def rel(symbol, v, w, matrix, nr):
    if symbol == 'left':
        return v[0] == 'L'
    if symbol == 'right':
        return v[0] == 'R'
    assert symbol == 'pairing'
    return v[0] == 'L' and w[0] == 'R' and beta(matrix, nr, v[1], w[1]) == 1


def nonunital_closure(generators):
    seen = set(generators) | {0}
    while True:
        new = seen | {a ^ b for a in seen for b in seen}
        new |= {a & b for a in seen for b in seen}
        if new == seen:
            return seen
        seen = new


def generated_tagged(generators):
    seen = set(generators) | {('L', 0), ('R', 0)}
    while True:
        old = len(seen)
        seen |= {op(s, v, w) for s in (('L', '+'), ('L', '*'),
                                      ('R', '+'), ('R', '*'))
                 for v in tuple(seen) for w in tuple(seen)}
        if len(seen) == old:
            return seen


def test_map(nl, nr, ml, mr, ol, or_, target):
    source = induced_matrix(target, mr, ol, or_, nl, nr)
    f = lambda v: (v[0], pull(v[1], ol if v[0] == 'L' else or_))
    domain = elems(nl, nr)
    assert len({f(v) for v in domain}) == len(domain)
    for s in (('L', '+'), ('L', '*'), ('R', '+'), ('R', '*')):
        for v in domain:
            for w in domain:
                assert f(op(s, v, w)) == op(s, f(v), f(w))
    assert f(('L', 0)) == ('L', 0) and f(('R', 0)) == ('R', 0)
    for v in domain:
        assert rel('left', v, v, source, nr) == rel('left', f(v), f(v), target, mr)
        assert rel('right', v, v, source, nr) == rel('right', f(v), f(v), target, mr)
        for w in domain:
            assert rel('pairing', v, w, source, nr) == rel('pairing', f(v), f(w), target, mr)
    return len(domain) ** 2


def main():
    stats = dict(morphisms=0, full_relation_checks=0, generated_substructures=0,
                 empty_tuple=0, zero_sort=0, nonunital_embeddings=0)
    for nl in range(3):
        for nr in range(3):
            for ml in range(nl, 4):
                for mr in range(nr, 4):
                    left_owners, right_owners = owner_maps(nl, ml), owner_maps(nr, mr)
                    for ol in (left_owners if len(left_owners) <= 4 else rng.sample(left_owners, 4)):
                        for or_ in (right_owners if len(right_owners) <= 4 else rng.sample(right_owners, 4)):
                            for _ in range(4):
                                target = rng.getrandbits(ml * mr)
                                f = lambda v: (v[0], pull(v[1], ol if v[0] == 'L' else or_))
                                stats['morphisms'] += 1
                                stats['full_relation_checks'] += test_map(
                                    nl, nr, ml, mr, ol, or_, target)
                                stats['zero_sort'] += int(nl == 0 or nr == 0)
                                stats['nonunital_embeddings'] += int(
                                    (-1 in ol) or (-1 in or_))
                                for _ in range(3):
                                    left = tuple(rng.randrange(1 << nl)
                                                 for _ in range(rng.randrange(3)))
                                    right = tuple(rng.randrange(1 << nr)
                                                  for _ in range(rng.randrange(3)))
                                    gens = [('L', x) for x in left] + [('R', y) for y in right]
                                    actual = generated_tagged(gens)
                                    expected = ({('L', x) for x in nonunital_closure(left)} |
                                                {('R', y) for y in nonunital_closure(right)})
                                    assert actual == expected
                                    assert {f(v) for v in actual} == generated_tagged(f(v) for v in gens)
                                    stats['generated_substructures'] += 1
                                    stats['empty_tuple'] += int(not gens)
    # A map exchanging tags fails the unary Left predicate, even when pairing is zero.
    assert rel('left', ('L', 0), ('L', 0), 0, 0)
    assert not rel('left', ('R', 0), ('R', 0), 0, 0)
    # Without preserving the pairing matrix, a native map is not a language embedding.
    assert rel('pairing', ('L', 1), ('R', 1), 1, 1) != rel(
        'pairing', ('L', 1), ('R', 1), 0, 1)
    # The empty tuple generates two distinct zero constants, not an empty carrier.
    assert generated_tagged([]) == {('L', 0), ('R', 0)}
    assert stats['zero_sort'] and stats['nonunital_embeddings'] and stats['empty_tuple']
    print('PASS finite tagged original-language encoding — semantic test only')
    for key, value in stats.items():
        print(key + ':', value)


if __name__ == '__main__':
    main()
