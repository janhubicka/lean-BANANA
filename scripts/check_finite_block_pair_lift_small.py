#!/usr/bin/env python3
"""Exhaustively challenge finite-block pairing automorphism lifts over F₂.

Represent vectors as bitsets. For each n <= 3, enumerate every invertible
n-by-n binary matrix. Determine its contragredient action on the other
sort and verify that extending both actions by the identity on up to
two outside coordinates preserves every pairing of all vectors.

This is an independent finite-model regression, not a Lean proof of the
general statement.
"""

from itertools import product


def parity(x: int) -> int:
    return x.bit_count() & 1


def apply_matrix(rows: tuple[int, ...], x: int) -> int:
    return sum(parity(row & x) << i for i, row in enumerate(rows))


def check() -> None:
    checks = 0
    groups = {}
    for n in range(4):
        invertible_count = 0
        for rows in product(range(1 << n), repeat=n):
            outputs = [apply_matrix(rows, x) for x in range(1 << n)]
            if len(set(outputs)) != (1 << n):
                continue
            invertible_count += 1
            # If the columns of the inverse are the preimages of basis
            # vectors, those columns are the *rows* of its transpose.
            dual_rows = tuple(outputs.index(1 << i) for i in range(n))
            low_mask = (1 << n) - 1
            for outside_dimension in range(3):
                total_dimension = n + outside_dimension
                for x in range(1 << total_dimension):
                    lift_left = (
                        apply_matrix(rows, x & low_mask)
                        | (x & ~low_mask)
                    )
                    for y in range(1 << total_dimension):
                        lift_right = (
                            apply_matrix(dual_rows, y & low_mask)
                            | (y & ~low_mask)
                        )
                        if parity(lift_left & lift_right) != parity(x & y):
                            raise AssertionError(
                                f"pairing failure n={n} k={outside_dimension}, "
                                f"A={rows}, x={x}, y={y}"
                            )
                        checks += 1
        groups[n] = invertible_count
    assert groups == {0: 1, 1: 1, 2: 6, 3: 168}, groups
    assert checks == 227913, checks
    print(f"OK: {checks} pairing checks over {sum(groups.values())} "
          "invertible finite blocks (n<=3, outside dimension<=2)")


if __name__ == "__main__":
    check()
