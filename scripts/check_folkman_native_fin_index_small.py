#!/usr/bin/env python3
"""Adversarial finite check: native Folkman pairings under all Fin atom orders.

Enumerate ALL bilinear F₂ matrices up to three atoms in each ring sort,
ALL permutations used to index the atoms, and ALL pairs of native ring
elements.  Check both Boolean-ring operations and full pairing values.
This is evidence only: the Lean module needs an actual kernel build.
"""
from itertools import permutations
from collections import Counter


def native_pairing(matrix, nleft, nright, x, y):
    parity = 0
    for a in range(nleft):
        if (x >> a) & 1:
            for b in range(nright):
                if (y >> b) & 1:
                    parity ^= (matrix >> (a * nright + b)) & 1
    return parity


def indexed_support(bits, atom_order):
    return sum(1 << atom_order[a]
               for a in range(len(atom_order)) if bits & (1 << a))


def check():
    totals = Counter()
    for nleft in range(4):
        for nright in range(4):
            for matrix in range(1 << (nleft * nright)):
                for eleft in permutations(range(nleft)):
                    for eright in permutations(range(nright)):
                        code = [[0 for _ in range(nright)]
                                for _ in range(nleft)]
                        for a in range(nleft):
                            for b in range(nright):
                                code[eleft[a]][eright[b]] = (
                                    matrix >> (a * nright + b)) & 1
                        for x in range(1 << nleft):
                            ix = indexed_support(x, eleft)
                            for y in range(1 << nright):
                                iy = indexed_support(y, eright)
                                transported = 0
                                for i in range(nleft):
                                    if ix & (1 << i):
                                        for j in range(nright):
                                            if iy & (1 << j):
                                                transported ^= code[i][j]
                                assert transported == native_pairing(
                                    matrix, nleft, nright, x, y)
                                totals["pairing_checks"] += 1
                        for x in range(1 << nleft):
                            for y in range(1 << nleft):
                                ix = indexed_support(x, eleft)
                                iy = indexed_support(y, eleft)
                                assert indexed_support(x ^ y, eleft) == ix ^ iy
                                assert indexed_support(x & y, eleft) == ix & iy
                                totals["ring_operation_checks"] += 1
                        totals["indexed_objects"] += 1
    assert totals["pairing_checks"] == 1231613
    assert totals["ring_operation_checks"] == 1245974
    assert totals["indexed_objects"] == 20165
    for k, value in totals.items():
        print(f"{k}: {value}")
    print("PASS: all zero-ring cases, matrices and Fin label choices")


if __name__ == "__main__":
    check()
