#!/usr/bin/env python3
"""Finite regression: intrinsic units transported by non-unital embeddings.
This is a semantic test and is NOT a Lean kernel proof.
"""
from itertools import product
from random import Random

if not __debug__:
    raise SystemExit("Regression checks require assertions; rerun without -O/PYTHONOPTIMIZE.")

rng = Random(20261108)

def closure(gens):
    seen = set(gens) | {0}
    while True:
        next_seen = seen | {a ^ b for a in seen for b in seen}
        next_seen |= {a & b for a in seen for b in seen}
        if next_seen == seen:
            return seen
        seen = next_seen

def apply_owner(x, owner):
    return sum(1 << j for j, i in enumerate(owner) if i >= 0 and x & (1 << i))

def join_all(xs):
    out = 0
    for x in xs:
        out |= x
    return out

def main():
    counts = dict(owner_maps=0, tuple_cases=0, source_zero_cases=0,
                  nonunital_target_cases=0, operation_checks=0)
    for n in range(4):
        for m in range(n, 5):
            for owner in product(range(-1, n), repeat=m):
                if not all(i in owner for i in range(n)):
                    continue
                counts["owner_maps"] += 1
                for k in range(4):
                    tuples = list(product(range(1 << n), repeat=k))
                    if len(tuples) > 35:
                        tuples = rng.sample(tuples, 35)
                    for xs in tuples:
                        S = closure(xs)
                        T = closure(tuple(apply_owner(x, owner) for x in xs))
                        assert T == {apply_owner(s, owner) for s in S}
                        assert len(S) == len(T)
                        u, v = join_all(S), join_all(T)
                        assert apply_owner(u, owner) == v
                        assert all((s & u) == s for s in S)
                        assert all((t & v) == t for t in T)
                        for a in S:
                            for b in S:
                                assert apply_owner(a ^ b, owner) == (apply_owner(a, owner) ^ apply_owner(b, owner))
                                assert apply_owner(a & b, owner) == (apply_owner(a, owner) & apply_owner(b, owner))
                                counts["operation_checks"] += 2
                        counts["tuple_cases"] += 1
                        counts["source_zero_cases"] += int(S == {0})
                        counts["nonunital_target_cases"] += int(v != ((1 << m) - 1))
    assert counts == dict(owner_maps=161, tuple_cases=9208, source_zero_cases=525,
                          nonunital_target_cases=6671, operation_checks=312530)
    print("PASS intrinsic-unit finite semantic regression (NOT Lean verification)")
    for k, v in counts.items():
        print(k, v)

if __name__ == "__main__":
    main()
