#!/usr/bin/env python3
"""Finite regression for BANANA copy ranges and their line-pair palettes.

This is independent of Lean. It enumerates small two-sorted F2 bilinear
systems and their injective pairing-preserving maps. A copy is identified by
the *pair of image subspaces*, not by an embedding. For every realisable
copy, the line-pair colour set computed from each embedding is checked to
agree with the intrinsic range-based set and to have at most the number of
source line pairs. These tests are not a proof of the general theorem.
"""
from itertools import product


def bit_parity(x):
    return x.bit_count() & 1


def eval_pair(matrix_rows, x, y):
    row_sum = 0
    for i, row in enumerate(matrix_rows):
        if x >> i & 1:
            row_sum ^= row
    return bit_parity(row_sum & y)


def span(basis):
    result = (0,)
    for v in basis:
        result = result + tuple(x ^ v for x in result)
    return result


def bases(n, d):
    if d == 0:
        yield (), (0,)
    else:
        for basis in product(range(1, 1 << n), repeat=d):
            values = span(basis)
            if len(set(values)) == (1 << d):
                yield basis, values


def induced_matrix(ambient_rows, left_basis, right_basis):
    return tuple(sum(eval_pair(ambient_rows, x, y) << j
                     for j, y in enumerate(right_basis))
                 for x in left_basis)


def palette(pairset, colour_function):
    return {colour_function(x, y) for x, y in pairset}


def check_ambient(nl, nr, matrices):
    checks = embeddings = groups_checked = 0
    bcase_count = 0
    for rows in matrices:
        for al in range(min(2, nl) + 1):
            for ar in range(min(2, nr) + 1):
                grouped = {}
                left_maps = list(bases(nl, al))
                right_maps = list(bases(nr, ar))
                for lbasis, lspan in left_maps:
                    for rbasis, rspan in right_maps:
                        embeddings += 1
                        source = induced_matrix(rows, lbasis, rbasis)
                        key = (source, frozenset(lspan), frozenset(rspan))
                        grouped.setdefault(key, []).append((lspan, rspan))
                for (source, lr, rr), maps in grouped.items():
                    groups_checked += 1
                    for b in (0, 1):
                        bcase_count += 1
                        ambient_pairs = {(x, y)
                                         for x in lr if x != 0
                                         for y in rr if y != 0
                                         if eval_pair(rows, x, y) == b}
                        source_pairs = sum(eval_pair(source, x, y) == b
                                           for x in range(1, 1 << al)
                                           for y in range(1, 1 << ar))
                        for lspan, rspan in maps:
                            from_source = {(lspan[x], rspan[y])
                                           for x in range(1, 1 << al)
                                           for y in range(1, 1 << ar)
                                           if eval_pair(source, x, y) == b}
                            assert from_source == ambient_pairs, (nl, nr, rows, al, ar, b)
                            colour_functions = (
                                lambda x, y: (3*x + 5*y) % 7,
                                lambda x, y: (x & y).bit_count() % 4,
                                lambda x, y: ((x << 2) ^ y) % 11,
                            )
                            for colour_function in colour_functions:
                                actual = palette(from_source, colour_function)
                                intrinsic = palette(ambient_pairs, colour_function)
                                assert actual == intrinsic
                                assert len(actual) <= source_pairs
                                checks += 1
    return embeddings, groups_checked, bcase_count, checks


def main():
    all_embeddings = all_groups = all_cases = all_checks = 0
    for nl, nr in [(1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3)]:
        if max(nl, nr) <= 2:
            matrices = [tuple((bits >> (i * nr)) & ((1 << nr)-1)
                              for i in range(nl))
                        for bits in range(1 << (nl * nr))]
        else:
            # Eight reproducible, structurally varied matrices at dimension 3.
            seed_codes = (0, 1, 2, 3, 5, 21, 37, (1 << (nl * nr))-1)
            matrices = [tuple((bits >> (i * nr)) & ((1 << nr)-1)
                              for i in range(nl))
                        for bits in seed_codes]
        embs, groups, cases, checks = check_ambient(nl, nr, matrices)
        all_embeddings += embs
        all_groups += groups
        all_cases += cases
        all_checks += checks
        print(f'PASS ambient=({nl},{nr}) matrices={len(matrices)} '
              f'embeddings={embs} copy ranges={groups} colour checks={checks}')
    print(f'PASS TOTAL embeddings={all_embeddings} ranges={all_groups} '
          f'parity cases={all_cases} palette comparisons={all_checks}')


if __name__ == '__main__':
    main()
