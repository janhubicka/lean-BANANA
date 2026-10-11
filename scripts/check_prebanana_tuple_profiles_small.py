#!/usr/bin/env python3
"""Exhaustive small finite-Boolean tuple-profile regression for pre-BANANA.

For every tuple length n=1,2,3, every ambient marked Boolean algebra
with 1..4 atoms and even total marking, and every n-tuple of subsets
of those atoms, compute the n-bit signature of each atom.

The tuple profile records:
  (a) precisely which membership signatures occur; and
  (b) the parity of the markings on each signature fibre.

Test every Boolean truth function on the n generator bits (all
2^(2^n) functions) both directly on ambient atoms and from this
record. In particular, the profile predicts element parity and
whether a term is zero. Compare independently encoded examples
sharing the same profile.

This validates small finite models, not the unrestricted Lean proof
or the subsequent Fraïssé/oligomorphic orbit argument.
"""
from collections import Counter, defaultdict
from itertools import product


def signatures(tuple_masks, atom_count):
    return tuple(
        sum(((m >> a) & 1) << i for i, m in enumerate(tuple_masks))
        for a in range(atom_count)
    )


def atom_eval(patterns, truth):
    return sum(1 << a for a, p in enumerate(patterns) if truth >> p & 1)


def profile(patterns, marks):
    present = sum(1 << p for p in set(patterns))
    marking = 0
    for a, p in enumerate(patterns):
        if marks >> a & 1:
            marking ^= 1 << p
    return present, marking


def main():
    checks = Counter()
    samples = defaultdict(list)
    for n in (1, 2, 3):
        truth_count = 1 << (1 << n)
        for m in range(1, 5):
            for tuple_masks in product(range(1 << m), repeat=n):
                patt = signatures(tuple_masks, m)
                for marks in range(1 << m):
                    if marks.bit_count() % 2:
                        continue
                    present, marking = profile(patt, marks)
                    key = (n, present, marking)
                    if len(samples[key]) < 2:
                        samples[key].append((m, tuple_masks, marks))
                    for truth in range(truth_count):
                        evaluated = atom_eval(patt, truth)
                        direct_parity = (evaluated & marks).bit_count() % 2
                        prof_parity = (marking & truth).bit_count() % 2
                        assert direct_parity == prof_parity
                        assert (evaluated == 0) == ((truth & present) == 0)
                        checks["term_profile_evaluations"] += 1
                    checks["marked_tuple_presentations"] += 1

    for (n, present, marking), pair in samples.items():
        if len(pair) != 2:
            continue
        (m1, t1, marks1), (m2, t2, marks2) = pair
        sig1, sig2 = signatures(t1, m1), signatures(t2, m2)
        for truth in range(1 << (1 << n)):
            v1 = atom_eval(sig1, truth)
            v2 = atom_eval(sig2, truth)
            assert (v1 & marks1).bit_count() % 2 == (
                (v2 & marks2).bit_count() % 2
            )
            assert (v1 == 0) == (v2 == 0)
            checks["cross_representation_checks"] += 1

    assert checks["marked_tuple_presentations"] == 37462
    assert checks["term_profile_evaluations"] == 8985832
    assert checks["cross_representation_checks"] == 217744
    print("finite pre-BANANA tuple profiles: PASS")
    print(f"  distinct tuple profiles: {len(samples):,}")
    for key in ("marked_tuple_presentations",
                "term_profile_evaluations",
                "cross_representation_checks"):
        print(f"  {key}: {checks[key]:,}")


if __name__ == "__main__":
    main()
