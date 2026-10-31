#!/usr/bin/env python3
"""Small finite regression for BANANA total/partial owner fibre identities.

Finite mathematical check only; not Lean kernel verification.
"""
from itertools import product

checks = 0
partial_checks = 0
for n in range(5):
    for m in range(4):
        if m == 0 and n > 0:
            total_maps = []
        else:
            total_maps = product(range(m), repeat=n)
        for f in total_maps:
            for target in product(range(2), repeat=m):
                source = tuple(target[f[x]] for x in range(n))
                for weights in product(range(3), repeat=n):
                    for a in range(2):
                        left = sum(
                            sum(weights[x] for x in range(n)
                                if target[b] == a and f[x] == b)
                            for b in range(m))
                        right = sum(weights[x] for x in range(n)
                                    if source[x] == a)
                        assert left == right, (n, m, f, target, weights, a)
                        checks += 1
        for owner in product(range(m + 1), repeat=n):
            # Owner value m represents Option.none.
            for weights in product(range(3), repeat=n):
                left = sum(sum(weights[x] for x in range(n)
                               if owner[x] == b) for b in range(m))
                right = sum(weights[x] for x in range(n) if owner[x] != m)
                assert left == right
                partial_checks += 1
print(f"Total-owner per-base identities passed: {checks}")
print(f"Partial-owner retained-fibre identities passed: {partial_checks}")
