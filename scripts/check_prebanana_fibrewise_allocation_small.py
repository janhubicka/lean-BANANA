#!/usr/bin/env python3
"""Exhaustive small adversarial audit of base-compatible pre-BANANA allocation.

Enumerates every surjective source/target projection, compatible witness
injection, distinguished target in *each* base fibre, and source F₂ marking
whose induced witness marks match the target's per-base parity, with:
  1 <= source atoms <= 5, 1 <= target atoms <= min(4, source atoms),
  1 <= base atoms <= min(2, target atoms).
This checks the exact quantifier shape of the abstract Lean fibrewise
allocation theorem, independently of its proof. It is not a Lean proof.
"""
from itertools import permutations, product


def parity(values):
    return sum(values) % 2


def main():
    compatible_diagrams = 0
    marked_allocations = 0
    for base_count in (1, 2):
        for source_count in range(base_count, 6):
            for target_count in range(base_count, min(source_count, 4) + 1):
                for source in product(range(base_count), repeat=source_count):
                    if len(set(source)) != base_count:
                        continue
                    for target in product(range(base_count), repeat=target_count):
                        if len(set(target)) != base_count:
                            continue
                        choices = [
                            tuple(b for b in range(target_count) if target[b] == a)
                            for a in range(base_count)
                        ]
                        for witness in permutations(range(source_count), target_count):
                            if any(source[witness[b]] != target[b]
                                   for b in range(target_count)):
                                continue
                            selected = {x: b for b, x in enumerate(witness)}
                            for base in product(*choices):
                                allocation = tuple(
                                    selected.get(x, base[source[x]])
                                    for x in range(source_count)
                                )
                                assert set(allocation) == set(range(target_count))
                                assert all(target[allocation[x]] == source[x]
                                           for x in range(source_count))
                                compatible_diagrams += 1
                                for mark_source in product((0, 1), repeat=source_count):
                                    mark_target = tuple(
                                        mark_source[witness[b]]
                                        for b in range(target_count)
                                    )
                                    if any(
                                        parity(mark_source[x] for x in range(source_count)
                                               if source[x] == a) !=
                                        parity(mark_target[b] for b in range(target_count)
                                               if target[b] == a)
                                        for a in range(base_count)
                                    ):
                                        continue
                                    assert all(
                                        parity(mark_source[x] for x in range(source_count)
                                               if allocation[x] == b) == mark_target[b]
                                        for b in range(target_count)
                                    )
                                    marked_allocations += 1
    assert compatible_diagrams == 17585, compatible_diagrams
    assert marked_allocations == 260226, marked_allocations
    print(f"PASS: {compatible_diagrams} base-compatible witness/section diagrams")
    print(f"PASS: {marked_allocations} completely marked allocation diagrams")

    # Referee counterexample: matching global parity does not imply
    # compatibility in individual base fibres.
    source, target = (0, 0, 1, 1), (0, 1)
    mark_source, mark_target = (0, 1, 0, 1), (0, 0)
    allocation = (0, 0, 1, 1)
    assert parity(mark_source) == parity(mark_target)
    assert [parity(mark_source[x] for x in range(4) if source[x] == a)
            for a in (0, 1)] == [1, 1]
    assert [parity(mark_target[b] for b in range(2) if target[b] == a)
            for a in (0, 1)] == [0, 0]
    assert any(parity(mark_source[x] for x in range(4)
                      if allocation[x] == b) != mark_target[b]
               for b in range(2))
    print("PASS: counterexample to insufficient global-parity hypothesis")


if __name__ == "__main__":
    main()
