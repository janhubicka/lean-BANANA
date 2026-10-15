#!/usr/bin/env python3
"""Adversarial finite test of the fibrewise pre-BANANA allocation.

Enumerate every surjective source/target map to a base set, every
compatible injective choice of one source witness per target atom,
and every source F₂ marking with compatible target marks, in sizes:
    1 <= source atoms <= 5
    1 <= target atoms <= min(3, source atoms)
    1 <= base atoms <= min(2, target atoms).

Test three independently formulated conclusions:
  1. every target atom gets a witness (surjective allocation),
  2. allocation commutes with both maps to the base,
  3. all allocation fibres have the prescribed F₂ mark.

The test is supplementary computational evidence, not a Lean proof.
"""
from itertools import permutations, product


def parity(values):
    return sum(values) & 1


def main():
    tested = 0
    maps_checked = 0
    for count_a in range(1, 6):
        for count_b in range(1, min(3, count_a) + 1):
            for count_d in range(1, min(2, count_b) + 1):
                for target in product(range(count_d), repeat=count_b):
                    if len(set(target)) != count_d:
                        continue
                    # Select the first atom over each base atom as the
                    # distinguished bin for the unselected leaves.
                    base = tuple(target.index(a) for a in range(count_d))
                    for source in product(range(count_d), repeat=count_a):
                        if len(set(source)) != count_d:
                            continue
                        for witness in permutations(range(count_a), count_b):
                            if any(source[witness[b]] != target[b]
                                   for b in range(count_b)):
                                continue
                            maps_checked += 1
                            selected = {leaf: b for b, leaf in enumerate(witness)}
                            allocation = [selected.get(x, base[source[x]])
                                          for x in range(count_a)]
                            assert {allocation[x] for x in witness} == set(range(count_b))
                            assert all(target[allocation[x]] == source[x]
                                       for x in range(count_a))

                            for source_mark in product((0, 1), repeat=count_a):
                                target_mark = tuple(source_mark[witness[b]]
                                                    for b in range(count_b))
                                if any(
                                    parity(source_mark[x] for x in range(count_a)
                                           if source[x] == a)
                                    != parity(target_mark[b] for b in range(count_b)
                                              if target[b] == a)
                                    for a in range(count_d)
                                ):
                                    continue

                                assert all(
                                    parity(source_mark[x] for x in range(count_a)
                                           if allocation[x] == b) == target_mark[b]
                                    for b in range(count_b)
                                )
                                tested += 1
    assert maps_checked == 2353, maps_checked
    assert tested == 25538, tested
    print(f"PASS: {maps_checked} compatible injective witness diagrams")
    print(f"PASS: {tested} parity-compatible marked fibre allocations")


if __name__ == "__main__":
    main()
