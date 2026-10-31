#!/usr/bin/env python3
"""Exhaustive small F2 pairing check of the stated coherent EPPA witness size.

For every l+r <= 3, every bilinear matrix, and every partial isomorphism
between two finite subpairs, test extension to a contragredient automorphism
of the perfect (l+r)-dimensional dot pairing. This checks *ordinary* EPPA
extension, not coherent choice of all extensions; Lean verification is separate.
"""
from itertools import product


def parity(x):
    return x.bit_count() & 1


def lin(cols, x):
    ans = 0
    for i, c in enumerate(cols):
        if x >> i & 1:
            ans ^= c
    return ans


def span(generators):
    values = {0}
    for v in generators:
        values |= {x ^ v for x in tuple(values)}
    return frozenset(values)


def basis(space):
    result = []
    seen = frozenset({0})
    for v in sorted(space):
        if v not in seen:
            result.append(v)
            seen = span(result)
    assert seen == space
    return tuple(result)


def spaces(n):
    all_spaces = {frozenset({0})}
    for v in range(1, 1 << n):
        all_spaces |= {span(s | {v}) for s in tuple(all_spaces)}
    return tuple(sorted(all_spaces, key=lambda s: (len(s), tuple(sorted(s)))))


def isomorphisms(src, dst):
    bs, bt = basis(src), basis(dst)
    if len(bs) != len(bt):
        return
    d = len(bs)
    for imgs in product(sorted(dst), repeat=d):
        if span(imgs) != dst:
            continue
        trans = {lin(bs, bits): lin(imgs, bits) for bits in range(1 << d)}
        assert set(trans) == src and set(trans.values()) == dst
        yield trans


def gl_actions(n):
    for cols in product(range(1 << n), repeat=n):
        f = tuple(lin(cols, x) for x in range(1 << n))
        if len(set(f)) != 1 << n:
            continue
        inv = [None] * (1 << n)
        for x, y in enumerate(f):
            inv[y] = x
        # The contragredient action on the second sort.
        right = tuple(sum(parity(inv[1 << i] & y) << i for i in range(n))
                      for y in range(1 << n))
        assert all(parity(f[x] & right[y]) == parity(x & y)
                   for x in range(1 << n) for y in range(1 << n))
        yield f, right


def pair_matrix_eval(rows, x, y):
    return parity(sum((parity(rows[i] & y) << i)
                      for i in range(len(rows))) & x)


def run():
    total = 0
    pairs = 0
    for n in range(4):
        ambient = tuple(gl_actions(n))
        for l in range(n + 1):
            r = n - l
            ls, rs = spaces(l), spaces(r)
            for rows in product(range(1 << r), repeat=l):
                pairs += 1
                # Natural embedding of A into its dot-product completion.
                emb_l = lambda x: x
                emb_r = lambda y: (sum((parity(rows[i] & y) << i)
                                      for i in range(l)) | (y << l))
                assert all(parity(emb_l(x) & emb_r(y)) ==
                           pair_matrix_eval(rows, x, y)
                           for x in range(1 << l) for y in range(1 << r))
                for u_l in ls:
                    for v_l in ls:
                        if len(u_l) != len(v_l):
                            continue
                        for fl in isomorphisms(u_l, v_l):
                            left_conditions = tuple((emb_l(x), emb_l(fl[x]))
                                                    for x in basis(u_l))
                            for u_r in rs:
                                for v_r in rs:
                                    if len(u_r) != len(v_r):
                                        continue
                                    for fr in isomorphisms(u_r, v_r):
                                        if any(pair_matrix_eval(rows, fl[x], fr[y]) !=
                                               pair_matrix_eval(rows, x, y)
                                               for x in u_l for y in u_r):
                                            continue
                                        right_conditions = tuple((emb_r(y), emb_r(fr[y]))
                                                                 for y in basis(u_r))
                                        assert any(all(L[x] == z for x, z in left_conditions)
                                                   and all(R[y] == z for y, z in right_conditions)
                                                   for L, R in ambient), (
                                                       l, r, rows, u_l, u_r,
                                                       v_l, v_r, fl, fr)
                                        total += 1
    print(f"All {total} partial isomorphisms extend in dimension l+r")
    print(f"Checked all {pairs} pairing matrices with l+r <= 3")
    print("This is a finite EPPA regression, not coherent EPPA or Lean validation")


if __name__ == "__main__":
    run()
