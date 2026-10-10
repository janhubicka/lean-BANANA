#!/usr/bin/env python3
"""Independent small-model adversarial regression for nested BANANA GL stages.

Exhaust all invertible F_2-matrices for each subset S of four labelled
coordinates with |S| <= 3. Use independently scrambled coordinate
enumerations for S and every T containing S. Compare global S-actions
against the induced T-stage actions, including the contragredient
right-sort maps. Also check every left/right cross-pairing.

This finite regression is not a proof of the general Lean theorem.
"""
from itertools import combinations, product


def parity(a: int) -> int:
    return a.bit_count() & 1


def apply(rows: tuple[int, ...], x: int) -> int:
    return sum(parity(row & x) << i for i, row in enumerate(rows))


def inverse_transpose(rows: tuple[int, ...], n: int):
    outputs = [apply(rows, x) for x in range(1 << n)]
    if len(set(outputs)) != 1 << n:
        return None
    return tuple(outputs.index(1 << i) for i in range(n))


def enumeration(indices, seed: int) -> list[int]:
    ordered = sorted(indices)
    if ordered:
        shift = (sum(ordered) + seed) % len(ordered)
        ordered = ordered[shift:] + ordered[:shift]
        if (sum(ordered) + seed) & 1:
            ordered.reverse()
    return ordered


def pack(x: int, ordered: list[int]) -> int:
    return sum(((x >> c) & 1) << i for i, c in enumerate(ordered))


def unpack(x: int, ordered: list[int]) -> int:
    return sum(((x >> i) & 1) << c for i, c in enumerate(ordered))


def lift(rows: tuple[int, ...], x: int, ordered: list[int], n: int) -> int:
    mask = sum(1 << c for c in ordered)
    return unpack(apply(rows, pack(x, ordered)), ordered) | (
        x & (((1 << n) - 1) ^ mask)
    )


def check() -> None:
    n = 4
    elements = 0
    pairing_checks = 0
    inclusion_checks = 0
    for k in range(n):
        for small in combinations(range(n), k):
            s_order = enumeration(small, 3)
            for rows in product(range(1 << k), repeat=k):
                dual = inverse_transpose(rows, k)
                if dual is None:
                    continue
                elements += 1
                for x in range(1 << n):
                    for y in range(1 << n):
                        left = lift(rows, x, s_order, n)
                        right = lift(dual, y, s_order, n)
                        assert parity(left & right) == parity(x & y), (
                            "pairing", small, rows, x, y
                        )
                        pairing_checks += 1
                for mask in range(1 << n):
                    larger = {i for i in range(n) if (mask >> i) & 1}
                    if not set(small).issubset(larger):
                        continue
                    t_order = enumeration(larger, 7)
                    m = len(t_order)
                    columns = [
                        pack(lift(rows, 1 << coord, s_order, n), t_order)
                        for coord in t_order
                    ]
                    large_rows = tuple(
                        sum(((columns[j] >> i) & 1) << j for j in range(m))
                        for i in range(m)
                    )
                    large_dual = inverse_transpose(large_rows, m)
                    assert large_dual is not None
                    for x in range(1 << n):
                        assert lift(rows, x, s_order, n) == lift(
                            large_rows, x, t_order, n
                        ), ("left inclusion", small, larger, rows, x)
                        assert lift(dual, x, s_order, n) == lift(
                            large_dual, x, t_order, n
                        ), ("right inclusion", small, larger, rows, x)
                        inclusion_checks += 2
    assert (elements, pairing_checks, inclusion_checks) == (
        713, 182528, 49152
    )
    print(f"OK: {elements} GL elements, {pairing_checks} pairing checks, "
          f"{inclusion_checks} nested-stage action checks")


if __name__ == "__main__":
    check()
