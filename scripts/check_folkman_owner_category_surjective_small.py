#!/usr/bin/env python3
"""Exhaustive small partial-owner identity and associativity regression.

This restricts to owner maps with nonempty fibres for every source atom.
It checks the owner component of embedding laws; a separate regression tests
pairing preservation of composition. Neither is a Lean kernel proof.
"""
from itertools import product


def owners(target, source):
    for o in product(range(source + 1), repeat=target):
        if all(i in o for i in range(source)):
            yield o


def compose(f, g, none):
    return tuple(none if j == len(f) else f[j] for j in g)


def test():
    checked = 0
    nontrivial = 0
    for a, b, c, d in product(range(4), repeat=4):
        if a + b + c + d > 10:
            continue
        for f in owners(b, a):
            for g in owners(c, b):
                for h in owners(d, c):
                    fg = compose(f, g, a)
                    gh = compose(g, h, b)
                    if compose(fg, h, a) != compose(f, gh, a):
                        raise AssertionError((a, b, c, d, f, g, h))
                    if compose(tuple(range(a)), f, a) != f:
                        raise AssertionError('left identity')
                    if compose(f, tuple(range(b)), a) != f:
                        raise AssertionError('right identity')
                    if not all(i in fg for i in range(a)):
                        raise AssertionError('two-stage surjectivity')
                    if not all(i in compose(fg, h, a) for i in range(a)):
                        raise AssertionError('three-stage surjectivity')
                    checked += 1
                    nontrivial += bool(a and b and c and d)
    return checked, nontrivial


if __name__ == '__main__':
    n, positive = test()
    print(f'Folkman owner category laws (nonempty fibres): {n:,} triples checked, '
          f'{positive:,} four-positive-sort triples')
