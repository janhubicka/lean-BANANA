#!/usr/bin/env python3
"""Exhaustive small models of finite non-unital Folkman hereditary closure.

Starts with arbitrary subsets containing zero, not preselected unital
subrings or atom partitions. These checks are not Lean kernel proofs.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
import json


@lru_cache(None)
def subrings(n: int) -> tuple[tuple[int, ...], ...]:
    size = 1 << n
    result = []
    for bits in range(1 << (size - 1)):
        members = (0,) + tuple(x for x in range(1, size)
                               if bits & (1 << (x - 1)))
        carrier = set(members)
        if all((x ^ y) in carrier and (x & y) in carrier
               for x in members for y in members):
            result.append(members)
    return tuple(result)


def pairing(matrix: int, right_atoms: int, x: int, y: int) -> int:
    return sum(((matrix >> (i * right_atoms)) & y).bit_count()
               for i in range(x.bit_length()) if x & (1 << i)) & 1


def check() -> Counter:
    stats = Counter()
    for n in range(5):
        for carrier in subrings(n):
            unit = 0
            for x in carrier:
                unit |= x
            assert unit in carrier
            identities = [e for e in carrier
                          if all((e & x) == x for x in carrier)]
            assert identities == [unit]
            assert (unit == (1 << n) - 1) == (((1 << n) - 1) in carrier)
            atoms = [a for a in carrier if a and not any(
                b != 0 and b != a and (b & a) == b for b in carrier)]
            codes = {x: sum(1 << i for i, a in enumerate(atoms)
                            if a & x == a) for x in carrier}
            assert set(codes.values()) == set(range(1 << len(atoms)))
            assert len(codes) == len(set(codes.values()))
            for x, y in product(carrier, repeat=2):
                assert codes[x ^ y] == codes[x] ^ codes[y]
                assert codes[x & y] == codes[x] & codes[y]
                stats['unchanged_operation_checks'] += 2
            stats['finite_subrings'] += 1
            stats['non_ambient_units'] += unit != (1 << n) - 1
            stats['zero_subrings'] += len(carrier) == 1
    for l, r in product(range(3), repeat=2):
        for sl, sr in product(subrings(l), subrings(r)):
            for matrix in range(1 << (l * r)):
                restricted = {(x, y): pairing(matrix, r, x, y)
                              for x, y in product(sl, sr)}
                for x, y in product(sl, sr):
                    for xx in sl:
                        assert restricted[x ^ xx, y] == (
                            restricted[x, y] ^ restricted[xx, y])
                        stats['pairing_additivity_checks'] += 1
                    for yy in sr:
                        assert restricted[x, y ^ yy] == (
                            restricted[x, y] ^ restricted[x, yy])
                        stats['pairing_additivity_checks'] += 1
                stats['pairing_restrictions'] += 1
    return stats


if __name__ == '__main__':
    print(json.dumps(dict(sorted(check().items())), indent=2))
    print('Finite model checks only: NOT a Lean kernel proof or independent referee.')
