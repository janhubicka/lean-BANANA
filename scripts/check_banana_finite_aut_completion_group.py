#!/usr/bin/env python3
"""Small exhaustive matrix check of finite BANANA automorphism groups.

For l+r<=3 enumerate every F2 bilinear pairing, every pairing-preserving
two-sorted linear automorphism, and every ordered pair of them.
Verify group closure and the perfect-completion action homomorphism.
These finite checks do not establish a Lean kernel theorem.
"""
from itertools import product


def parity(x):
    return x.bit_count() & 1


def composition(f, g):
    return tuple(f[g[x]] for x in range(len(f)))


def inverse(f):
    g = [None] * len(f)
    for x, y in enumerate(f):
        g[y] = x
    return tuple(g)


def linear_action(cols, n):
    out = []
    for x in range(1 << n):
        v = 0
        for i in range(n):
            if x >> i & 1:
                v ^= cols[i]
        out.append(v)
    return tuple(out)


def gl(n):
    for cols in product(range(1 << n), repeat=n):
        a = linear_action(cols, n)
        if len(set(a)) == 1 << n:
            yield a


def contra(f, n):
    finv = inverse(f)
    return tuple(
        sum(parity(finv[1 << i] & y) << i for i in range(n))
        for y in range(1 << n)
    )


def dot(x, y):
    return parity(x & y)


def eval_pair(rows, x, y):
    return parity(sum(parity(row & y) << i for i, row in enumerate(rows)) & x)


def completion_pair(f, g, l, r):
    cg = contra(g, r)
    left = tuple(f[x & ((1 << l) - 1)] |
                 (cg[x >> l] << l) for x in range(1 << (l + r)))
    return left, contra(left, l + r)


def pair_preserving(f, g, rows, l, r):
    return all(eval_pair(rows, f[x], g[y]) == eval_pair(rows, x, y)
               for x in range(1 << l) for y in range(1 << r))


group_elements = 0
multiplications = 0
base_cases = 0

for n in range(4):
    for l in range(n + 1):
        r = n - l
        gl_left = tuple(gl(l))
        gl_right = tuple(gl(r))
        for rows in product(range(1 << r), repeat=l):
            base_cases += 1
            G = tuple((f, g) for f in gl_left for g in gl_right
                      if pair_preserving(f, g, rows, l, r))
            assert G
            Gset = set(G)
            group_elements += len(G)
            completed = {a: completion_pair(*a, l, r) for a in G}
            ident_left = tuple(range(1 << l))
            ident_right = tuple(range(1 << r))
            assert (ident_left, ident_right) in Gset
            for f, g in G:
                inv = (inverse(f), inverse(g))
                assert inv in Gset
                L, R = completed[f, g]
                assert all(dot(L[x], R[y]) == dot(x, y)
                           for x in range(1 << n) for y in range(1 << n))
                # Original left embedding x |-> (x, 0).
                assert all(L[x] == f[x] for x in range(1 << l))
                # Right embedding y |-> ((A*y), y).
                def right_embedding(y):
                    return (sum(parity(row & y) << i for i, row in enumerate(rows)) |
                            (y << l))
                assert all(R[right_embedding(y)] == right_embedding(g[y])
                           for y in range(1 << r))
                for h, k in G:
                    prod = (composition(f, h), composition(g, k))
                    assert prod in Gset
                    Lp, Rp = completed[prod]
                    Lh, Rh = completed[h, k]
                    assert Lp == composition(L, Lh)
                    assert Rp == composition(R, Rh)
                    multiplications += 1

print(f"Pairing matrices: {base_cases}")
print(f"Individual finite automorphisms checked: {group_elements}")
print(f"Group closure and completion homomorphism pairs: {multiplications}")
print("Checks finite group and action laws only, not coherent groupoid choices")
