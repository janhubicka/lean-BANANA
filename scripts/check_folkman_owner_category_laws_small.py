#!/usr/bin/env python3
"""Regression for identity and associativity of Option-valued atom owners.

Independent finite arithmetic check only. It does not compile Lean.
"""
from itertools import product


def maps(n, m):
    return product(range(m + 1), repeat=n)


def compose(f, g, none):
    return tuple(none if j == len(f) else f[j] for j in g)


def main():
    checked = 0
    for q, m, n, p in product(range(4), repeat=4):
        if max(q, m, n, p) > 2 and q + m + n + p > 6:
            continue
        for f in maps(m, q):
            for g in maps(n, m):
                for h in maps(p, n):
                    assert compose(compose(f, g, q), h, q) == compose(
                        f, compose(g, h, m), q)
                    assert compose(tuple(range(q)), f, q) == f
                    assert compose(f, tuple(range(m)), q) == f
                    checked += 1
    print(f'Owner identity and associativity: {checked} exhaustive triples passed')


if __name__ == '__main__':
    main()
