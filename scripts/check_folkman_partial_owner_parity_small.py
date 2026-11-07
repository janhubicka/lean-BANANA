#!/usr/bin/env python3
"""Finite regression for partial ownership and unused Folkman atoms.

A standalone arithmetic test, NOT a Lean kernel proof nor a native-ring map
verification. The sentinel q denotes Option.none (unowned target atoms).
"""
from itertools import product, combinations


def subsets(n):
    for k in range(n + 1):
        yield from combinations(range(n), k)


def check():
    checked = 0
    negative = 0
    for nl in range(3):
        for nr in range(3):
            for ql in range(3):
                for qr in range(3):
                    for ol in product(range(ql + 1), repeat=nl):
                        for or_ in product(range(qr + 1), repeat=nr):
                            for bits in product((0, 1), repeat=nl * nr):
                                for ls in subsets(ql):
                                    for rs in subsets(qr):
                                        xl = tuple(i for i, o in enumerate(ol)
                                                   if o < ql and o in ls)
                                        yr = tuple(j for j, o in enumerate(or_)
                                                   if o < qr and o in rs)
                                        natural = sum(bits[i*nr+j] for i in xl for j in yr)
                                        fibre = sum(
                                            sum(bits[i*nr+j] for i in range(nl)
                                                for j in range(nr)
                                                if ol[i] == a and or_[j] == b)
                                            for a in ls for b in rs)
                                        parity = 0
                                        for i in xl:
                                            for j in yr:
                                                parity ^= bits[i*nr+j]
                                        if natural != fibre or natural % 2 != parity:
                                            raise ValueError((
                                                'partial-owner identity', nl, nr, ql, qr,
                                                ol, or_, bits, ls, rs))
                                        checked += 1
                                        # Negative control: incorrectly treat unowned
                                        # target atoms as belonging to a source fibre.
                                        if ql and qr and nl and nr and ql-1 in ls and qr-1 in rs:
                                            bad_xl = tuple(i for i,o in enumerate(ol)
                                                           if o in ls or o == ql)
                                            bad_yr = tuple(j for j,o in enumerate(or_)
                                                           if o in rs or o == qr)
                                            bad_sum = sum(bits[i*nr+j] for i in bad_xl
                                                          for j in bad_yr)
                                            if bad_sum % 2 != natural % 2:
                                                negative += 1
    if negative == 0:
        raise ValueError('negative control not detected')
    return checked, negative


if __name__ == '__main__':
    checked, negative = check()
    print(f'Partial-owner F2 incidence: {checked} exhaustive cases; '
          f'{negative} invalid-owner negative controls detected')
