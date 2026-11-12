#!/usr/bin/env python3
"""Independent finite regression for the Folkman edge-count cast identity.

This tests finite instances only; it does not establish Lean elaboration or
kernel correctness. It deliberately avoids importing the Lean implementation.
"""
from itertools import combinations, product


def subsets(n):
    for k in range(n + 1):
        yield from combinations(range(n), k)


def check():
    examined = 0
    for left in range(4):
        for right in range(4):
            for cells in product((0, 1), repeat=left * right):
                for xs in subsets(left):
                    for ys in subsets(right):
                        # Count ordinary incident edges and map that integer to F_2.
                        count = sum(1 for i in xs for j in ys if cells[i * right + j] == 1)
                        # Independently evaluate the F_2 matrix sum.
                        parity = 0
                        for i in xs:
                            for j in ys:
                                parity ^= cells[i * right + j]
                        if count % 2 != parity:
                            raise RuntimeError((left, right, cells, xs, ys, count, parity))
                        examined += 1
    return examined


if __name__ == '__main__':
    print(f'Folkman edge-count F2 cast: {check()} exhaustive configurations passed')
