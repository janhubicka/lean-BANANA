#!/usr/bin/env python3
"""Adversarial finite check for the two-sort Folkman pairing extension.

For base atom counts 0 or 1 per sort, and 1 or 2 atoms in each of B
and C on each sort, enumerate all partial atom-owner maps and all
F₂-bilinear forms on B and C. Retain pairings agreeing on the common
base, then verify existence of a pairing on the actual atom-grid-plus-
private-points amalgam by solving the full binary linear equation
system for its matrix entries.

The test verifies existence, not a particular Lean construction.
"""
from itertools import product


def owners(n, m):
    options = (-1,) if m == 0 else (-1, 0)
    return [v for v in product(options, repeat=n) if m == 0 or 0 in v]


def amalgam_atoms(f, g, m):
    inside = [(b, c) for b in range(len(f)) for c in range(len(g))
              if f[b] == g[c] and 0 <= f[b] < m]
    outside_left = [(b, None) for b in range(len(f)) if f[b] == -1]
    outside_right = [(None, c) for c in range(len(g)) if g[c] == -1]
    return inside + outside_left + outside_right


def binary_linear_system_consistent(rows):
    pivots = {}
    for mask, value in rows:
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (mask, value)
                break
            old_mask, old_value = pivots[pivot]
            mask ^= old_mask
            value ^= old_value
        else:
            if value:
                return False
    return True


def main():
    compatible = candidates = 0
    for al, ar in product((0, 1), repeat=2):
        for nb_l, nb_r, nc_l, nc_r in product((1, 2), repeat=4):
            for fl in owners(nb_l, al):
                for fr in owners(nb_r, ar):
                    for gl in owners(nc_l, al):
                        for gr in owners(nc_r, ar):
                            left = amalgam_atoms(fl, gl, al)
                            right = amalgam_atoms(fr, gr, ar)
                            masks_b = [
                                sum(1 << (i * len(right) + j)
                                    for i, x in enumerate(left)
                                    for j, y in enumerate(right)
                                    if x[0] == b and y[0] == c)
                                for b in range(nb_l) for c in range(nb_r)
                            ]
                            masks_c = [
                                sum(1 << (i * len(right) + j)
                                    for i, x in enumerate(left)
                                    for j, y in enumerate(right)
                                    if x[1] == b and y[1] == c)
                                for b in range(nc_l) for c in range(nc_r)
                            ]
                            for bits_b in range(1 << len(masks_b)):
                                for bits_c in range(1 << len(masks_c)):
                                    candidates += 1
                                    agree = all(
                                        (sum((bits_b >> (x * nb_r + y)) & 1
                                             for x in range(nb_l) if fl[x] == i
                                             for y in range(nb_r) if fr[y] == j) % 2)
                                        ==
                                        (sum((bits_c >> (x * nc_r + y)) & 1
                                             for x in range(nc_l) if gl[x] == i
                                             for y in range(nc_r) if gr[y] == j) % 2)
                                        for i in range(al) for j in range(ar)
                                    )
                                    if not agree:
                                        continue
                                    rows = (
                                        [(mask, (bits_b >> i) & 1)
                                         for i, mask in enumerate(masks_b)]
                                        +
                                        [(mask, (bits_c >> i) & 1)
                                         for i, mask in enumerate(masks_c)]
                                    )
                                    assert binary_linear_system_consistent(rows), (
                                        al, ar, fl, fr, gl, gr, bits_b, bits_c
                                    )
                                    compatible += 1
    assert candidates == 38288, candidates
    assert compatible == 23838, compatible
    print(f"PASS: all {compatible} compatible pairings extend "
          f"(among {candidates} small two-sort diagrams)")


if __name__ == "__main__":
    main()
