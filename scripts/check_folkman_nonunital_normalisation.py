#!/usr/bin/env python3
"""Finite semantic checks for the Track C non-unital closure bridge.

The Boolean evaluator, polynomial compiler, direct ring closure and
signature-fibre isomorphism are separate implementations. This script
does NOT execute Lean or certify the new Lean declarations.
"""
from __future__ import annotations

from functools import cache
from itertools import product
from random import Random

from check_folkman_tuple_term_completeness_small import blocks, closure

Term = tuple
Polynomial = frozenset[int]  # nonempty sets of variables; no constant monomial
ZERO: Polynomial = frozenset()


@cache
def multiply(p: Polynomial, q: Polynomial) -> Polynomial:
    out: set[int] = set()
    for a in p:
        for b in q:
            m = a | b
            if m in out:
                out.remove(m)
            else:
                out.add(m)
    return frozenset(out)


def centred_product(c: int, d: int, p: Polynomial, q: Polynomial) -> Polynomial:
    return multiply(p, q) ^ (q if c else ZERO) ^ (p if d else ZERO)


@cache
def compile_term(t: Term) -> tuple[int, Polynomial]:
    op = t[0]
    if op == 'zero':
        return 0, ZERO
    if op == 'one':
        return 1, ZERO
    if op == 'var':
        return 0, frozenset({1 << t[1]})
    c, p = compile_term(t[1])
    if op == 'not':
        return 1 ^ c, p
    d, q = compile_term(t[2])
    cross = centred_product(c, d, p, q)
    if op == 'and':
        return c & d, cross
    if op == 'or':
        return c | d, p ^ q ^ cross
    raise ValueError(f'Unknown Boolean constructor: {op}')


@cache
def truth_table(t: Term, n: int) -> int:
    full = (1 << (1 << n)) - 1
    op = t[0]
    if op == 'zero':
        return 0
    if op == 'one':
        return full
    if op == 'var':
        return sum(1 << a for a in range(1 << n) if a & (1 << t[1]))
    a = truth_table(t[1], n)
    if op == 'not':
        return full ^ a
    b = truth_table(t[2], n)
    return (a & b) if op == 'and' else (a | b)


@cache
def polynomial_table(p: Polynomial, n: int) -> int:
    assert all(m != 0 and m < (1 << n) for m in p)
    return sum((sum((a & m) == m for m in p) % 2) << a
               for a in range(1 << n))


def dnf(table: int, n: int) -> Term:
    out: Term = ('zero',)
    for a in range(1 << n):
        if not (table >> a) & 1:
            continue
        clause: Term = ('one',)
        for i in range(n):
            literal: Term = ('var', i)
            if not (a >> i) & 1:
                literal = ('not', literal)
            clause = ('and', clause, literal)
        out = ('or', out, clause)
    return out


def random_term(rng: Random, n: int, depth: int) -> Term:
    if depth == 0 or rng.randrange(4) == 0:
        choice = rng.randrange(n + 2)
        return ('var', choice - 2) if choice >= 2 else (('zero',) if choice == 0 else ('one',))
    op = rng.choice(('not', 'and', 'or'))
    left = random_term(rng, n, depth - 1)
    return (op, left) if op == 'not' else (op, left, random_term(rng, n, depth - 1))


def check_compiler(t: Term, n: int) -> None:
    c, p = compile_term(t)
    table = truth_table(t, n)
    full = (1 << (1 << n)) - 1
    assert c == (table & 1)
    assert polynomial_table(p, n) == table ^ (full if c else 0)


def main() -> None:
    tables_checked = constructor_checks = closure_checks = 0
    iso_checks = operation_checks = generator_checks = 0
    for n in range(4):
        full = (1 << (1 << n)) - 1
        compiled = []
        for table in range(1 << (1 << n)):
            t = dnf(table, n)
            assert truth_table(t, n) == table
            check_compiler(t, n)
            check_compiler(('not', t), n)
            compiled.append(compile_term(t))
            tables_checked += 1
        for a, (c, p) in enumerate(compiled):
            for b, (d, q) in enumerate(compiled):
                cross = centred_product(c, d, p, q)
                assert polynomial_table(cross, n) == ((a & b) ^ (full if c & d else 0))
                assert polynomial_table(p ^ q ^ cross, n) == ((a | b) ^ (full if c | d else 0))
                constructor_checks += 2
        representatives: dict[tuple[int, ...], tuple[dict[int, int], set[int]]] = {}
        for atoms in range(4):
            for xs in product(range(1 << atoms), repeat=n):
                fs = blocks(atoms, xs)
                generated = closure(xs)
                by_functions = set()
                for table in range(0, 1 << (1 << n), 2):
                    # Select exactly those nonzero pattern fibres where f is true.
                    by_functions.add(sum(mask for p, mask in fs.items() if (table >> p) & 1))
                assert generated == by_functions
                closure_checks += 1
                key = tuple(sorted(fs))
                target, target_ring = representatives.setdefault(key, (fs, generated))
                mapping = {x: sum(mask for p, mask in target.items() if x & fs[p])
                           for x in generated}
                assert mapping[0] == 0
                assert set(mapping.values()) == target_ring
                assert len(mapping) == len(target_ring)
                for i, x in enumerate(xs):
                    assert mapping[x] == sum(mask for p, mask in target.items() if (p >> i) & 1)
                    generator_checks += 1
                for x in generated:
                    for y in generated:
                        assert mapping[x ^ y] == mapping[x] ^ mapping[y]
                        assert mapping[x & y] == mapping[x] & mapping[y]
                        operation_checks += 2
                iso_checks += 1
    rng = Random(20261102)
    random_checks = 0
    for n in range(5):
        for _ in range(1000):
            check_compiler(random_term(rng, n, 6), n)
            random_checks += 1
    # Unit and omitted-cross-term mutations must be rejected.
    assert closure(()) == closure((0,)) == {0}
    x, y = frozenset({1}), frozenset({2})
    assert polynomial_table(centred_product(1, 0, x, y), 2) != polynomial_table(multiply(x, y), 2)
    assert tables_checked == 278 and constructor_checks == 131624
    assert closure_checks == iso_checks == 689
    print('all Boolean truth tables (0-3 variables):', tables_checked)
    print('binary-constructor semantic checks:', constructor_checks)
    print('seeded syntactic term checks (0-4 variables):', random_checks)
    print('non-unital generated-closure cases:', closure_checks)
    print('finite powerset ring isomorphism cases:', iso_checks)
    print('addition/multiplication preservation checks:', operation_checks)
    print('named-generator preservation checks:', generator_checks)
    print('PASS; finite semantic regression only, not Lean kernel verification')


if __name__ == '__main__':
    main()
