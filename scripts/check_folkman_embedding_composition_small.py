#!/usr/bin/env python3
"""Exhaustive finite check: pairing-preserving Folkman atom embeddings compose.

Construct B's edge matrix by aggregating C along g's disjoint, nonempty
owner fibres; construct A analogously from B and f. Compare the composite
matrix directly with A. These are finite tests, not Lean kernel proofs.
"""
from itertools import product


def owners(target_count, source_count):
    for assignment in product(range(source_count + 1), repeat=target_count):
        if all(i in assignment for i in range(source_count)):
            yield assignment


def aggregate(edges, left_count, right_count, left_owner, right_owner,
              source_left, source_right):
    return tuple(
        sum(edges[i * right_count + j]
            for i in range(left_count) if left_owner[i] == a
            for j in range(right_count) if right_owner[j] == b) % 2
        for a in range(source_left) for b in range(source_right)
    )


def compose(f, g, none):
    return tuple(none if j == len(f) else f[j] for j in g)


def main():
    diagrams = 0
    comparisons = 0
    for aL, aR, bL, bR, cL, cR in product(range(3), repeat=6):
        for fl in owners(bL, aL):
            for fr in owners(bR, aR):
                for gl in owners(cL, bL):
                    for gr in owners(cR, bR):
                        hl = compose(fl, gl, aL)
                        hr = compose(fr, gr, aR)
                        assert all(i in hl for i in range(aL))
                        assert all(i in hr for i in range(aR))
                        for matrix in product((0, 1), repeat=cL * cR):
                            mid = aggregate(matrix, cL, cR, gl, gr, bL, bR)
                            source = aggregate(mid, bL, bR, fl, fr, aL, aR)
                            direct = aggregate(matrix, cL, cR, hl, hr, aL, aR)
                            if source != direct:
                                raise RuntimeError((aL, aR, bL, bR, cL, cR,
                                                    fl, fr, gl, gr, matrix))
                            diagrams += 1
                            comparisons += len(source)
    print(f'Composed pairing-preserving embeddings: {diagrams} diagrams, '
          f'{comparisons} source matrix entries passed')


if __name__ == '__main__':
    main()
