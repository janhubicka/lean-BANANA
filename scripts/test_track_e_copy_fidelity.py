#!/usr/bin/env python3
"""Independent exhaustive small-model checks for BANANA Track E.

These checks concern finite F_2 pairings and unlabelled copies. They are
regression evidence, not a replacement for a Lean kernel check.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product


@dataclass(frozen=True)
class Pairing:
    left: int
    right: int
    rows: tuple[int, ...]

    def evaluate(self, x: int, y: int) -> int:
        result = 0
        for i, row in enumerate(self.rows):
            if x & (1 << i):
                result ^= (row & y).bit_count() % 2
        return result


def span(columns: tuple[int, ...]) -> frozenset[int]:
    vectors = {0}
    for column in columns:
        vectors |= {v ^ column for v in list(vectors)}
    return frozenset(vectors)


def apply_map(columns: tuple[int, ...], x: int) -> int:
    result = 0
    for i, column in enumerate(columns):
        if x & (1 << i):
            result ^= column
    return result


@lru_cache(maxsize=None)
def injections(source: int, target: int) -> tuple[tuple[int, ...], ...]:
    return tuple(columns for columns in product(range(1 << target), repeat=source)
                 if len(span(columns)) == (1 << source))


@lru_cache(maxsize=None)
def embeddings(A: Pairing, C: Pairing) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    return tuple((f, g) for f in injections(A.left, C.left)
                 for g in injections(A.right, C.right)
                 if all(C.evaluate(f[i], g[j]) == (A.rows[i] >> j) & 1
                        for i in range(A.left) for j in range(A.right)))


def copy_of_embedding(A: Pairing, f: tuple[int, ...], g: tuple[int, ...]):
    return (span(f), span(g))


@lru_cache(maxsize=None)
def copies(A: Pairing, C: Pairing) -> frozenset:
    return frozenset(copy_of_embedding(A, f, g) for f, g in embeddings(A, C))


def all_pairings(max_dimension: int = 2) -> tuple[Pairing, ...]:
    return tuple(Pairing(l, r, rows)
                 for l in range(max_dimension + 1)
                 for r in range(max_dimension + 1)
                 for rows in product(range(1 << r), repeat=l))


def change_basis(A: Pairing, f: tuple[int, ...], g: tuple[int, ...]) -> Pairing:
    assert A.left == len(f) and A.right == len(g)
    assert len(span(f)) == 1 << A.left and len(span(g)) == 1 << A.right
    inverse_f = {apply_map(f, x): x for x in range(1 << A.left)}
    inverse_g = {apply_map(g, y): y for y in range(1 << A.right)}
    rows = tuple(sum(A.evaluate(inverse_f[1 << i], inverse_g[1 << j]) << j
                     for j in range(A.right)) for i in range(A.left))
    return Pairing(A.left, A.right, rows)


def matrix_rank(rows: tuple[int, ...]) -> int:
    """Independent Gaussian-elimination invariant for a rectangular F_2 matrix."""
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row
                break
            row ^= pivots[p]
    return len(pivots)


@lru_cache(maxsize=None)
def subspaces_with_bases(d: int, n: int):
    """Enumerate each d-plane exactly once, independently of pairing data."""
    result = {}
    for basis in injections(d, n):
        result.setdefault(span(basis), basis)
    return tuple(result.items())


def rank_copies(A: Pairing, C: Pairing):
    """A restricted pairing is isomorphic to A iff its rank agrees."""
    expected = set()
    for U, f in subspaces_with_bases(A.left, C.left):
        for V, g in subspaces_with_bases(A.right, C.right):
            restricted = tuple(
                sum(C.evaluate(x, y) << j for j, y in enumerate(g))
                for x in f)
            if matrix_rank(restricted) == matrix_rank(A.rows):
                expected.add((U, V))
    return frozenset(expected)


def line_pairs(A: Pairing, b: int) -> tuple[tuple[int, int], ...]:
    return tuple((x, y) for x in range(1, 1 << A.left)
                 for y in range(1, 1 << A.right) if A.evaluate(x, y) == b)


def induced_palette(C: Pairing, D: tuple[frozenset, frozenset], b: int):
    # Deliberately non-invariant under basis changes: an ambient colouring.
    colour = lambda x, y: (x + 3 * y + (x ^ y).bit_count()) % 7
    return frozenset(colour(x, y) for x in D[0] if x != 0
                     for y in D[1] if y != 0 if C.evaluate(x, y) == b)


def run() -> dict[str, int]:
    structures = all_pairings(2)
    # Negative controls: embedding-count is not copy-count, and
    # two nonisomorphic pairings cannot be identified by dimension.
    nonrigid = Pairing(2, 0, (0, 0))
    assert len(embeddings(nonrigid, nonrigid)) == 6
    assert len(copies(nonrigid, nonrigid)) == 1
    A_zero = Pairing(1, 1, (0,))
    A_one = Pairing(1, 1, (1,))
    assert not copies(A_zero, A_one)
    assert len(copies(A_one, A_one)) == 1
    counts = dict(structures=len(structures), source_target_pairs=0,
                  source_basis_changes=0, source_basis_checks=0,
                  basis_pairing_checks=0, precomposition_checks=0,
                  ambient_basis_checks=0, ambient_copy_bijection_checks=0,
                  rank_classification_checks=0,
                  one_sided_checks=0, palette_checks=0,
                  embedding_composition_checks=0)
    for A in structures:
        for C in structures:
            copy_set = copies(A, C)
            assert copy_set == rank_copies(A, C), (A, C, copy_set, rank_copies(A, C))
            counts['rank_classification_checks'] += 1
            counts['source_target_pairs'] += 1
            for f, g in embeddings(A, C):
                assert copy_of_embedding(A, f, g) in copy_set
            if A.left == 0 or A.right == 0:
                if A.right == 0:
                    expected = frozenset((W, frozenset({0}))
                          for f in injections(A.left, C.left) for W in [span(f)])
                else:
                    expected = frozenset((frozenset({0}), W)
                          for g in injections(A.right, C.right) for W in [span(g)])
                assert copy_set == expected, (A, C)
                counts['one_sided_checks'] += 1
            for D in copy_set:
                for b in (0, 1):
                    assert len(induced_palette(C, D, b)) <= len(line_pairs(A, b)), (A, C, D, b)
                    counts['palette_checks'] += 1
    for A in structures:
        for f in injections(A.left, A.left):
            for g in injections(A.right, A.right):
                A_prime = change_basis(A, f, g)
                counts['source_basis_changes'] += 1
                for x in range(1 << A.left):
                    for y in range(1 << A.right):
                        assert A_prime.evaluate(apply_map(f, x), apply_map(g, y)) == A.evaluate(x, y), (A, A_prime, f, g, x, y)
                        counts['basis_pairing_checks'] += 1
                for C in structures:
                    assert copies(A, C) == copies(A_prime, C), (A, A_prime, C)
                    counts['source_basis_checks'] += 1
                    for eL, eR in embeddings(A_prime, C):
                        preL = tuple(apply_map(eL, v) for v in f)
                        preR = tuple(apply_map(eR, v) for v in g)
                        assert copy_of_embedding(A, preL, preR) == copy_of_embedding(A_prime, eL, eR)
                        assert all(C.evaluate(preL[i], preR[j]) == ((A.rows[i] >> j) & 1)
                                   for i in range(A.left) for j in range(A.right))
                        counts['precomposition_checks'] += 1
    # Independent ambient-coordinate refactor: image sets move under a
    # pairing-preserving invertible change of coordinates, bijectively.
    for B in structures:
        for f in injections(B.left, B.left):
            for g in injections(B.right, B.right):
                B_prime = change_basis(B, f, g)
                counts['ambient_basis_checks'] += 1
                for A in structures:
                    transported = frozenset(
                        (frozenset(apply_map(f, x) for x in D[0]),
                         frozenset(apply_map(g, y) for y in D[1]))
                        for D in copies(A, B))
                    assert transported == copies(A, B_prime), (A, B, B_prime, f, g)
                    counts['ambient_copy_bijection_checks'] += 1
    # Check composition for all small sources/targets in sorts of dimension <= 1.
    small = tuple(A for A in structures if A.left <= 1 and A.right <= 1)
    for A in small:
        for B in small:
            for eL, eR in embeddings(A, B):
                for C in structures:
                    for fL, fR in embeddings(B, C):
                        compL = tuple(apply_map(fL, x) for x in eL)
                        compR = tuple(apply_map(fR, x) for x in eR)
                        D = copy_of_embedding(A, eL, eR)
                        mappedD = (frozenset(apply_map(fL, x) for x in D[0]),
                                   frozenset(apply_map(fR, y) for y in D[1]))
                        assert mappedD == copy_of_embedding(A, compL, compR)
                        assert mappedD in copies(A, C)
                        counts['embedding_composition_checks'] += 1
    return counts


if __name__ == '__main__':
    for key, value in run().items():
        print(f'{key}: {value}')
    print('PASS: exhaustive finite regression; no kernel verification claimed')
