#!/usr/bin/env python3
"""Finite semantic check for native atom codes and independently chosen term representatives.

This is a regression for the Track C source, NOT Lean kernel verification.
"""
from itertools import permutations, product
from random import Random

rng = Random(20261103)


def evaluate(term, xs):
    if term[0] == "zero":
        return 0
    if term[0] == "var":
        return xs[term[1]]
    a, b = evaluate(term[1], xs), evaluate(term[2], xs)
    return a ^ b if term[0] == "add" else a & b


def add(a, b):
    return ("add", a, b)


def mul(a, b):
    return ("mul", a, b)


ZERO = ("zero",)


def permute(x, perm):
    return sum(1 << perm[a] for a in range(len(perm)) if x & (1 << a))


def random_term(k, depth):
    if depth == 0 or rng.randrange(5) == 0:
        return ZERO if k == 0 or rng.randrange(5) == 0 else ("var", rng.randrange(k))
    a, b = random_term(k, depth - 1), random_term(k, depth - 1)
    return add(a, b) if rng.randrange(2) else mul(a, b)


def model(k, patterns):
    pats = list(patterns) + [
        rng.choice(list(patterns) + [0]) for _ in range(rng.randrange(4))
    ]
    rng.shuffle(pats)
    xs = tuple(sum(1 << a for a, p in enumerate(pats) if (p >> i) & 1)
               for i in range(k))
    blocks = {p: sum(1 << a for a, q in enumerate(pats) if q == p)
              for p in patterns}
    return xs, blocks


def fibre_term(k, p):
    assert p != 0
    i = next(i for i in range(k) if (p >> i) & 1)
    t = ("var", i)
    for j in range(k):
        if j == i:
            continue
        v = ("var", j)
        t = mul(t, v) if (p >> j) & 1 else add(t, mul(t, v))
    return t


def union_term(k, selected):
    t = ZERO
    for p in selected:
        t = add(t, fibre_term(k, p))
    return t


def perturb(t, k):
    # Insert nontrivial-looking but semantically zero subexpressions.
    for _ in range(rng.randrange(6)):
        v = random_term(k, 4)
        case = rng.randrange(4)
        if case == 0:
            t = add(t, ZERO)
        elif case == 1:
            t = add(add(t, v), v)
        elif case == 2:
            t = add(t, add(v, v))
        else:
            t = add(t, mul(ZERO, v))
    return t


def main():
    commute = profiles = operation_checks = representative_checks = generator_checks = 0
    for atoms in range(5):
        perms = list(permutations(range(atoms)))
        for k in range(4):
            tuples = list(product(range(1 << atoms), repeat=k))
            if len(tuples) > 800:
                tuples = rng.sample(tuples, 800)
            for xs in tuples:
                perm = rng.choice(perms)
                ys = tuple(permute(x, perm) for x in xs)
                for _ in range(30):
                    t = random_term(k, 5)
                    assert permute(evaluate(t, xs), perm) == evaluate(t, ys)
                    commute += 1

    for k in range(4):
        for _ in range(300):
            patterns = frozenset(p for p in range(1, 1 << k)
                                 if rng.randrange(3) != 0)
            xs, blocks_x = model(k, patterns)
            ys, blocks_y = model(k, patterns)
            subsets = [
                tuple(p for i, p in enumerate(sorted(patterns))
                      if (idx >> i) & 1)
                for idx in range(1 << len(patterns))
            ]
            source_to_target = {}
            for selected in subsets:
                x = sum(blocks_x[p] for p in selected)
                y = sum(blocks_y[p] for p in selected)
                canonical = union_term(k, selected)
                assert evaluate(canonical, xs) == x
                assert evaluate(canonical, ys) == y
                chosen = perturb(canonical, k)
                assert evaluate(chosen, xs) == x
                assert evaluate(chosen, ys) == y
                source_to_target[x] = y, chosen
                representative_checks += 1
            assert len(source_to_target) == len(subsets)
            assert len({y for y, _ in source_to_target.values()}) == len(subsets)
            assert source_to_target[0][0] == 0
            for i in range(k):
                assert source_to_target[xs[i]][0] == ys[i]
                generator_checks += 1
            elements = list(source_to_target)
            for _ in range(30):
                x, z = rng.choice(elements), rng.choice(elements)
                fx, fz = source_to_target[x][0], source_to_target[z][0]
                assert source_to_target[x ^ z][0] == fx ^ fz
                assert source_to_target[x & z][0] == fx & fz
                assert evaluate(source_to_target[x ^ z][1], ys) == fx ^ fz
                assert evaluate(source_to_target[x & z][1], ys) == fx & fz
                operation_checks += 4
            profiles += 1

    assert (commute, profiles, representative_checks, operation_checks,
            generator_checks) == (52860, 1200, 12084, 144000, 1800)
    print("native atom-code evaluations:", commute)
    print("equal-pattern pairs:", profiles)
    print("arbitrary representative checks:", representative_checks)
    print("operation-preservation assertions:", operation_checks)
    print("generator checks:", generator_checks)
    print("PASS; not a Lean kernel check")


# Fail closed rather than silently skipping every Python assert under -O.
if not __debug__:
    raise SystemExit("Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.")

if __name__ == "__main__":
    main()
