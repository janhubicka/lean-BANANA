#!/usr/bin/env python3
"""Exhaustive finite arithmetic check of composed partial atom owners.

Target atoms have an Option-valued owner. Composition must propagate None,
including when the intermediate target atom exists but is not owned.
This checks arithmetic, not whether actual native Boolean-ring maps exist.
"""
from itertools import product


def compose(first, second, sentinel):
    """first: intermediate atoms -> source owners; second: target -> intermediate."""
    return tuple(sentinel if b == len(first) or first[b] == sentinel
                 else first[b] for b in second)


def run():
    checked = 0
    negatives = 0
    for al, ar, bl, br, cl, cr in product(range(3), repeat=6):
        for fL in product(range(al + 1), repeat=bl):
            for fR in product(range(ar + 1), repeat=br):
                for gL in product(range(bl + 1), repeat=cl):
                    for gR in product(range(br + 1), repeat=cr):
                        hL = compose(fL, gL, al)
                        hR = compose(fR, gR, ar)
                        for bits in product((0, 1), repeat=cl * cr):
                            # Sum target matrix entries by direct composite owners.
                            # Also check the equivalent two-stage partition sum.
                            for a in range(al):
                                for b in range(ar):
                                    direct = sum(bits[i*cr+j] for i in range(cl)
                                                 for j in range(cr)
                                                 if hL[i] == a and hR[j] == b)
                                    staged = sum(bits[i*cr+j]
                                                 for x in range(bl) if fL[x] == a
                                                 for y in range(br) if fR[y] == b
                                                 for i in range(cl) if gL[i] == x
                                                 for j in range(cr) if gR[j] == y)
                                    if direct != staged:
                                        raise AssertionError((al, ar, bl, br, cl, cr,
                                                              fL, fR, gL, gR, bits, a, b))
                                    checked += 1
                                    # Deliberately wrong: map intermediate None to
                                    # final owner 0, producing fake owned atoms.
                                    if al and ar:
                                        wrongL = tuple(0 if gL[i] == bl else hL[i]
                                                       for i in range(cl))
                                        wrongR = tuple(0 if gR[j] == br else hR[j]
                                                       for j in range(cr))
                                        wrong = sum(bits[i*cr+j] for i in range(cl)
                                                    for j in range(cr)
                                                    if wrongL[i] == a and wrongR[j] == b)
                                        if wrong % 2 != direct % 2:
                                            negatives += 1
    if negatives == 0:
        raise AssertionError('negative control was ineffective')
    print(f'Composed partial-owner pairings: {checked} source-pair cases passed; '
          f'{negatives} incorrect-None cases distinguished')


if __name__ == '__main__':
    run()
