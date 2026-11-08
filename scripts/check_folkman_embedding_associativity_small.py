#!/usr/bin/env python3
"""Independent finite test of threefold pairing-preserving composition.

Every owner map has nonempty source fibres. For each final binary pairing
matrix, reconstruct three intermediate matrices by summing over owner fibres,
then compare with direct aggregation along the composite owner maps.
Arithmetic evidence only: not a Lean build or a native ring-map proof.
"""
from itertools import product


def owners(target, source):
    return (o for o in product(range(source + 1), repeat=target)
            if all(i in o for i in range(source)))


def comp(f, g, none):
    return tuple(none if j == len(f) else f[j] for j in g)


def aggregate(matrix, right_size, ol, or_, sl, sr):
    return tuple(sum(matrix[i * right_size + j]
                     for i in range(len(ol)) if ol[i] == a
                     for j in range(len(or_)) if or_[j] == b) % 2
                 for a in range(sl) for b in range(sr))


def main():
    diagrams = entries = positive = 0
    # Exhaust all eight sort sizes in {0,1}; supplement with small size-two
    # configurations without an infeasible Cartesian explosion.
    sizes = list(product(range(2), repeat=8))
    sizes += [(a, b, c, d, a, b, c, d)
              for a, b, c, d in product(range(3), repeat=4)
              if max(a, b, c, d) == 2]
    for aL, aR, bL, bR, cL, cR, dL, dR in sizes:
        for fl in owners(bL, aL):
            for fr in owners(bR, aR):
                for gl in owners(cL, bL):
                    for gr in owners(cR, bR):
                        for hl in owners(dL, cL):
                            for hr in owners(dR, cR):
                                left = comp(comp(fl, gl, aL), hl, aL)
                                right = comp(comp(fr, gr, aR), hr, aR)
                                assert left == comp(fl, comp(gl, hl, bL), aL)
                                assert right == comp(fr, comp(gr, hr, bR), aR)
                                for matrix in product((0, 1), repeat=dL * dR):
                                    C = aggregate(matrix, dR, hl, hr, cL, cR)
                                    B = aggregate(C, cR, gl, gr, bL, bR)
                                    A = aggregate(B, bR, fl, fr, aL, aR)
                                    direct = aggregate(matrix, dR, left, right,
                                                       aL, aR)
                                    if A != direct:
                                        raise AssertionError(
                                            (aL, aR, bL, bR, cL, cR, dL, dR,
                                             fl, fr, gl, gr, hl, hr, matrix))
                                    diagrams += 1
                                    entries += len(A)
                                    positive += bool(all((aL, aR, bL, bR,
                                                          cL, cR, dL, dR)))
    print(f'Threefold pairing composition: {diagrams} diagrams, '
          f'{entries} entries, {positive} all-positive diagrams passed')


if __name__ == '__main__':
    main()
