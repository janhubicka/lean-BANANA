#!/usr/bin/env python3
"""Adversarial finite semantics for tagged Folkman substructures.

Closed tagged subsets are exactly pairs of non-unital Boolean subrings,
and tagged generated closures equal the two native generated subrings.
Pairing relations impose no additional closure requirements.
This is NOT a Lean kernel proof.
"""
from itertools import combinations, product
from collections import Counter

if not __debug__:
    raise SystemExit("Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.")


def ring_closure(gens):
    seen = {0} | set(gens)
    while True:
        nxt = seen | {a ^ b for a in seen for b in seen}
        nxt |= {a & b for a in seen for b in seen}
        if nxt == seen:
            return seen
        seen = nxt


def is_subring(r):
    return 0 in r and all((a ^ b) in r and (a & b) in r for a in r for b in r)


def apply_op(symbol, a, b):
    sort, kind = symbol
    if a[0] != sort or b[0] != sort:
        return (sort, 0)
    return (sort, a[1] ^ b[1] if kind == '+' else a[1] & b[1])


def tagged_closure(gens):
    elems = {('L', 0), ('R', 0)} | set(gens)
    while True:
        nxt = elems | {apply_op(symbol, a, b)
                       for symbol in (('L', '+'), ('L', '*'), ('R', '+'), ('R', '*'))
                       for a in elems for b in elems}
        if nxt == elems:
            return elems
        elems = nxt


def tagged_closed(elems):
    return {('L', 0), ('R', 0)} <= elems and all(
        apply_op(symbol, a, b) in elems
        for symbol in (('L', '+'), ('L', '*'), ('R', '+'), ('R', '*'))
        for a in elems for b in elems)


def all_sets(xs):
    xs = tuple(xs)
    for k in range(len(xs) + 1):
        yield from (set(c) for c in combinations(xs, k))


def main():
    stats = Counter()
    for nl in range(4):
        for nr in range(4):
            L = range(1 << nl)
            R = range(1 << nr)
            sets_L = list(all_sets(range(1, 1 << nl)))
            sets_R = list(all_sets(range(1, 1 << nr)))
            if nl == 3:
                sets_L = [s for s in sets_L if len(s) <= 2]
                sets_L += [ring_closure(gs) - {0} for k in range(3)
                           for gs in product(L, repeat=k)]
            if nr == 3:
                sets_R = [s for s in sets_R if len(s) <= 2]
                sets_R += [ring_closure(gs) - {0} for k in range(3)
                           for gs in product(R, repeat=k)]
            sets_L = list({frozenset(s) for s in sets_L})
            sets_R = list({frozenset(s) for s in sets_R})
            for left in sets_L:
                for right in sets_R:
                    SL, SR = set(left) | {0}, set(right) | {0}
                    tagged = {('L', x) for x in SL} | {('R', y) for y in SR}
                    assert tagged_closed(tagged) == (is_subring(SL) and is_subring(SR))
                    stats['candidate_tagged_substructures'] += 1
                    if tagged_closed(tagged):
                        stats['actual_tagged_substructures'] += 1
                        assert {x for t, x in tagged if t == 'L'} == SL
                        assert {y for t, y in tagged if t == 'R'} == SR
            tuples_L = [x for k in range(3) for x in product(L, repeat=k)]
            tuples_R = [y for k in range(3) for y in product(R, repeat=k)]
            for xs in tuples_L:
                for ys in tuples_R:
                    gens = [('L', x) for x in xs] + [('R', y) for y in ys]
                    actual = tagged_closure(gens)
                    expected = ({('L', x) for x in ring_closure(xs)} |
                                {('R', y) for y in ring_closure(ys)})
                    assert actual == expected
                    stats['generated_closure_comparisons'] += 1
                    stats['empty_tuple'] += not gens
                    stats['zero_ring_sort'] += (nl == 0 or nr == 0)
    assert stats['candidate_tagged_substructures'] == 2209
    assert stats['actual_tagged_substructures'] == 529
    assert stats['generated_closure_comparisons'] == 10816
    assert stats['empty_tuple'] == 16
    print('PASS tagged first-order substructure and closure semantics (NOT Lean)')
    for key, value in sorted(stats.items()):
        print(key + ':', value)


if __name__ == '__main__':
    main()
