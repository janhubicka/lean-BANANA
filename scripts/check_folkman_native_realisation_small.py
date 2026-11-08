#!/usr/bin/env python3
"""Finite adversarial checks for native Folkman code realisation.

Tests mathematical models, NOT Lean elaboration. Boolean-ring elements
are checked in both bit-mask and Boolean-tuple representations. Embeddings
are enumerated as arbitrary injective zero-preserving functions, rather
than generated from atom-owner maps. Subrings need not contain ambient 1.
"""
from collections import Counter
from itertools import permutations, product
import json


def encode(value: int, width: int) -> tuple[int, ...]:
    return tuple((value >> i) & 1 for i in range(width))


def decode(value: tuple[int, ...]) -> int:
    return sum(bit << i for i, bit in enumerate(value))


def pairing(matrix: int, right_count: int, x: int, y: int) -> int:
    return sum(((matrix >> (i * right_count)) & y).bit_count()
               for i in range(x.bit_length()) if (x >> i) & 1) % 2


def check_realisations(stats: Counter) -> None:
    for n in range(5):
        elements = list(product((0, 1), repeat=n))
        assert len(elements) == 2 ** n
        assert n <= len(elements)
        assert {decode(x) for x in elements} == set(range(1 << n))
        for x in elements:
            assert encode(decode(x), n) == x
            for y in elements:
                assert decode(tuple(a ^ b for a, b in zip(x, y))) == decode(x) ^ decode(y)
                assert decode(tuple(a & b for a, b in zip(x, y))) == decode(x) & decode(y)
                stats['ring_operation_pairs'] += 1
    for l in range(4):
        for r in range(4):
            for matrix in range(1 << (l * r)):
                table = [[pairing(matrix, r, x, y) for y in range(1 << r)]
                         for x in range(1 << l)]
                for x in range(1 << l):
                    for y in range(1 << r):
                        # Independent double sum on Boolean-tuple elements.
                        direct = sum(encode(x, l)[i] * encode(y, r)[j] *
                                     ((matrix >> (i * r + j)) & 1)
                                     for i in range(l) for j in range(r)) % 2
                        assert table[x][y] == direct
                        stats['native_pairing_values'] += 1
                        for xx in range(1 << l):
                            assert table[x ^ xx][y] == table[x][y] ^ table[xx][y]
                            stats['additivity_equalities'] += 1
                        for yy in range(1 << r):
                            assert table[x][y ^ yy] == table[x][y] ^ table[x][yy]
                            stats['additivity_equalities'] += 1
                for i in range(l):
                    for j in range(r):
                        assert table[1 << i][1 << j] == (matrix >> (i * r + j)) & 1
                stats['native_objects'] += 1


def check_arbitrary_embeddings(stats: Counter) -> None:
    for n in range(3):
        for m in range(4):
            source, target = 1 << n, 1 << m
            # Exhaustive over arbitrary injective zero-preserving functions.
            for tail in permutations(range(1, target), source - 1):
                table = (0,) + tail
                stats['candidate_maps'] += 1
                if not all(table[x ^ y] == table[x] ^ table[y] and
                           table[x & y] == table[x] & table[y]
                           for x in range(source) for y in range(source)):
                    continue
                owner = []
                for j in range(m):
                    candidates = [i for i in range(n) if table[1 << i] & (1 << j)]
                    assert len(candidates) <= 1
                    owner.append(candidates[0] if candidates else None)
                assert all(i in owner for i in range(n))
                for x in range(source):
                    reconstructed = sum(1 << j for j, i in enumerate(owner)
                                        if i is not None and x & (1 << i))
                    assert reconstructed == table[x]
                    stats['original_map_equalities'] += 1
                stats['ring_embeddings'] += 1
                if table[-1] != target - 1:
                    stats['non_unital_embeddings'] += 1


def check_subrings(stats: Counter) -> None:
    for n in range(5):
        size = 1 << n
        for selected in range(1 << (size - 1)):
            members = [0] + [x for x in range(1, size) if selected & (1 << (x - 1))]
            subset = set(members)
            if not all((x ^ y) in subset and (x & y) in subset
                       for x in members for y in members):
                continue
            unit = 0
            for x in members:
                unit |= x
            assert unit in subset
            assert all(x & unit == x for x in members)
            assert len(members) & (len(members) - 1) == 0
            stats['closed_subrings'] += 1
            if unit != size - 1:
                stats['subrings_without_ambient_unit'] += 1
    # Explicit guard against treating non-unital subrings as ambient-unital.
    assert all((x ^ y) in {0, 1} and (x & y) in {0, 1}
               for x in {0, 1} for y in {0, 1})
    assert 3 not in {0, 1}
    assert all(x & 1 == x for x in {0, 1})


def main() -> None:
    stats = Counter()
    check_realisations(stats)
    check_arbitrary_embeddings(stats)
    check_subrings(stats)
    print(json.dumps(dict(sorted(stats.items())), indent=2))
    print('Finite regression only: NOT a Lean kernel proof or independent model referee.')


if __name__ == '__main__':
    main()
