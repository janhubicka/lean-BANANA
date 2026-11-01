#!/usr/bin/env python3
"""Exhaustive S3 two-sort checks for i_V^{-1} p i_U representative codes.

This only checks change-of-representative permutation algebra, NOT
preservation of the BANANA pairing or linear operations.
"""
from itertools import permutations

H = tuple(permutations(range(3)))
e = (0, 1, 2)
c = ((1, 2, 0), (2, 0, 1), (1, 0, 2))


def mul(a, b):
    return tuple(a[b[i]] for i in range(3))


def inv(a):
    b = [None] * 3
    for i, j in enumerate(a):
        b[j] = i
    return tuple(b)


def core(iu, iv, p):
    return mul(mul(inv(iv), p), iu)


checks = 0
for il_u in H:
    for il_v in H:
        for il_w in H:
            # Choose an unrelated family of changes on the right sort.
            ir_u = mul(c[0], il_u)
            ir_v = mul(c[1], il_v)
            ir_w = mul(c[2], il_w)
            assert core(il_u, il_u, e) == e
            assert core(ir_u, ir_u, e) == e
            for p in H:
                for q in H:
                    assert core(il_u, il_w, mul(q, p)) == \
                        mul(core(il_v, il_w, q), core(il_u, il_v, p))
                    assert core(ir_u, ir_w, mul(q, p)) == \
                        mul(core(ir_v, ir_w, q), core(ir_u, ir_v, p))
                    checks += 2

print(f"Two-sort representative-code composition checks: {checks}")
print("Pairing and linearity of the codes remain independent obligations")
