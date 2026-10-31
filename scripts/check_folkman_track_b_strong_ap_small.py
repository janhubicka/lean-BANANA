#!/usr/bin/env python3
"""Independent finite adversarial audit of Folkman--BANANA strong AP.

Test the original non-unital two-sort Boolean-ring language via powerset
models. Construct fibre grids and private atoms and solve the COMPLETE F2
bilinear-extension system. This is a regression, not Lean verification.
"""
from collections import Counter
from itertools import product


def owners(a, b):
    return [x for x in product(range(-1, a), repeat=b)
            if all(i in x for i in range(a))]


def sort_diagram(a, b, c, f, g):
    atoms = ([('grid', ib, ic) for ib in range(b) for ic in range(c)
              if f[ib] != -1 and f[ib] == g[ic]]
             + [('privateB', ib) for ib in range(b) if f[ib] == -1]
             + [('privateC', ic) for ic in range(c) if g[ic] == -1])
    bi = tuple(sum(1 << k for k, z in enumerate(atoms)
                   if (z[0] == 'grid' and z[1] == ib)
                   or (z[0] == 'privateB' and z[1] == ib))
               for ib in range(b))
    ci = tuple(sum(1 << k for k, z in enumerate(atoms)
                   if (z[0] == 'grid' and z[2] == ic)
                   or (z[0] == 'privateC' and z[1] == ic))
               for ic in range(c))
    assert all(bi) and all(ci)
    assert all((x & y) == 0 for i, x in enumerate(bi)
               for j, y in enumerate(bi) if i != j)
    assert all((x & y) == 0 for i, x in enumerate(ci)
               for j, y in enumerate(ci) if i != j)

    def image(x, blocks):
        return sum(mask for i, mask in enumerate(blocks) if (x >> i) & 1)

    base_b = tuple(image(sum(1 << i for i in range(b) if f[i] == j), bi)
                   for j in range(a))
    base_c = tuple(image(sum(1 << i for i in range(c) if g[i] == j), ci)
                   for j in range(a))
    assert base_b == base_c
    assert all(base_b)
    bs = [image(x, bi) for x in range(1 << b)]
    cs = [image(x, ci) for x in range(1 << c)]
    common = {image(x, base_b) for x in range(1 << a)}
    assert set(bs) & set(cs) == common, (a, b, c, f, g)
    for supports in (bs, cs):
        assert len(set(supports)) == len(supports)
        for x in range(len(supports)):
            for y in range(len(supports)):
                assert supports[x ^ y] == supports[x] ^ supports[y]
                assert supports[x & y] == supports[x] & supports[y]
    return len(atoms), bi, ci, base_b, bs, cs


def pairing(matrix, nright, x, y):
    result = 0
    for i in range(x.bit_length()):
        if (x >> i) & 1:
            for j in range(y.bit_length()):
                if (y >> j) & 1:
                    result ^= (matrix >> (i * nright + j)) & 1
    return result


def row_for(ls, rs, nleft, nright):
    row = 0
    for i in range(nleft):
        if (ls >> i) & 1:
            for j in range(nright):
                if (rs >> j) & 1:
                    row ^= 1 << (i * nright + j)
    return row


def solve(rows, bits):
    basis = {}
    for row, value in zip(rows, bits):
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (row, value)
                break
            oldrow, oldvalue = basis[pivot]
            row ^= oldrow
            value ^= oldvalue
        if row == 0 and value:
            return None
    solution = 0
    for pivot, (row, value) in sorted(basis.items()):
        if value ^ ((row & solution).bit_count() & 1):
            solution |= 1 << pivot
    for row, value in zip(rows, bits):
        assert ((row & solution).bit_count() & 1) == value
    return solution


def run():
    stats = Counter()
    diagrams = []
    for a in range(3):
        for b in range(a, 3):
            for c in range(a, 3):
                for f in owners(a, b):
                    for g in owners(a, c):
                        diagrams.append((a, b, c, f, g,
                                         sort_diagram(a, b, c, f, g)))
    for al, bl, cl, fl, gl, L in diagrams:
        for ar, br, cr, fr, gr, R in diagrams:
            dl, bimL, cimL, baseL, bsubL, csubL = L
            dr, bimR, cimR, baseR, bsubR, csubR = R
            rows = ([row_for(x, y, dl, dr) for x in bimL for y in bimR] +
                    [row_for(x, y, dl, dr) for x in cimL for y in cimR])
            stats['diagrams'] += 1
            for mb in range(1 << (bl * br)):
                for mc in range(1 << (cl * cr)):
                    bits = ([(mb >> (i * br + j)) & 1
                             for i in range(bl) for j in range(br)] +
                            [(mc >> (i * cr + j)) & 1
                             for i in range(cl) for j in range(cr)])
                    compatible = all(
                        pairing(mb, br,
                                sum(1 << i for i in range(bl) if fl[i] == a),
                                sum(1 << j for j in range(br) if fr[j] == r)) ==
                        pairing(mc, cr,
                                sum(1 << i for i in range(cl) if gl[i] == a),
                                sum(1 << j for j in range(cr) if gr[j] == r))
                        for a in range(al) for r in range(ar))
                    matrix = solve(rows, bits)
                    if not compatible:
                        assert matrix is None
                        stats['incompatible'] += 1
                        continue
                    assert matrix is not None
                    for x in range(1 << bl):
                        for y in range(1 << br):
                            assert pairing(mb, br, x, y) == \
                                pairing(matrix, dr, bsubL[x], bsubR[y])
                    for x in range(1 << cl):
                        for y in range(1 << cr):
                            assert pairing(mc, cr, x, y) == \
                                pairing(matrix, dr, csubL[x], csubR[y])
                    stats['compatible_pairings'] += 1
    return stats


if __name__ == '__main__':
    stats = run()
    print('Folkman finite strong AP:', dict(stats))
    print('Independent finite regression only; NOT a Lean kernel proof.')
