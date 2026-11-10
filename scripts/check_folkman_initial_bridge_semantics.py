#!/usr/bin/env python3
"""Finite semantics for initial paired bridges from generated isomorphisms.

The same positive membership-pattern code is embedded twice into
different finite subrings of one ambient two-sort Boolean-ring pairing.
It verifies ring operations, generators and ALL F2 pairing values.
This is NOT a Lean kernel check or independent referee certification.
"""
from random import Random

if not __debug__:
    raise SystemExit("Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.")

rng = Random(20261110)


def fibres(xs, atoms):
    out = {}
    for a in range(atoms):
        p = sum(((x >> a) & 1) << i for i, x in enumerate(xs))
        if p:
            out[p] = out.get(p, 0) | (1 << a)
    return out


def encode(cells):
    pat = sorted(cells)
    return {s: sum(cells[p] for i, p in enumerate(pat) if s >> i & 1)
            for s in range(1 << len(pat))}


def pairing(matrix, nr, x, y):
    return sum((matrix >> (i * nr + j)) & 1
               for i in range(x.bit_length()) if x >> i & 1
               for j in range(y.bit_length()) if y >> j & 1) & 1


def matrix_of(left, right, mat, nr):
    return {(p, q): pairing(mat, nr, left[p], right[q])
            for p in left for q in right}


def check_codes(la, ra, lb, rb, mat, nr):
    assert la.keys() == lb.keys() and ra.keys() == rb.keys()
    L1, L2, R1, R2 = map(encode, (la, lb, ra, rb))
    for code in (L1, L2, R1, R2):
        assert len(set(code.values())) == len(code)
        for a in code:
            for b in code:
                assert code[a ^ b] == code[a] ^ code[b]
                assert code[a & b] == code[a] & code[b]
    M = matrix_of(la, ra, mat, nr)
    assert M == matrix_of(lb, rb, mat, nr)
    lp, rp = sorted(la), sorted(ra)
    for a in L1:
        for b in R1:
            target = sum(M[(p, q)] for i, p in enumerate(lp) if a >> i & 1
                         for j, q in enumerate(rp) if b >> j & 1) & 1
            assert pairing(mat, nr, L1[a], R1[b]) == target
            assert pairing(mat, nr, L2[a], R2[b]) == target
    return len(L1) * len(R1)


def main():
    count = dict(attempts=0, valid=0, pairing_cases=0, zero_sort=0,
                 unequal_fibre_sizes=0, generator_only_misses=0)
    for nl in range(5):
        for nr in range(5):
            for _ in range(220):
                kl, kr = rng.randrange(3), rng.randrange(3)
                aL = tuple(rng.randrange(1 << nl) for _ in range(kl))
                bL = tuple(rng.randrange(1 << nl) for _ in range(kl))
                aR = tuple(rng.randrange(1 << nr) for _ in range(kr))
                bR = tuple(rng.randrange(1 << nr) for _ in range(kr))
                la, lb = fibres(aL, nl), fibres(bL, nl)
                ra, rb = fibres(aR, nr), fibres(bR, nr)
                if la.keys() != lb.keys() or ra.keys() != rb.keys():
                    continue
                mat = rng.getrandbits(nl * nr)
                count["attempts"] += 1
                if matrix_of(la, ra, mat, nr) != matrix_of(lb, rb, mat, nr):
                    if all(pairing(mat, nr, x, y) == pairing(mat, nr, xx, yy)
                           for x, xx in zip(aL, bL) for y, yy in zip(aR, bR)):
                        count["generator_only_misses"] += 1
                    continue
                count["pairing_cases"] += check_codes(la, ra, lb, rb, mat, nr)
                count["valid"] += 1
                count["zero_sort"] += int(not la or not ra)
                count["unequal_fibre_sizes"] += int(
                    [v.bit_count() for v in la.values()] !=
                    [v.bit_count() for v in lb.values()] or
                    [v.bit_count() for v in ra.values()] !=
                    [v.bit_count() for v in rb.values()])
    # A valid initial bridge does not imply global homogeneity.
    assert check_codes(fibres((1,), 3), {}, fibres((3,), 3), {}, 0, 0) == 2
    assert count == dict(attempts=2740, valid=2602, pairing_cases=4548,
                         zero_sort=2485, unequal_fibre_sizes=676,
                         generator_only_misses=1)
    print("PASS finite initial bridge semantics (NOT a Lean proof)")
    print(count)


if __name__ == "__main__":
    main()
