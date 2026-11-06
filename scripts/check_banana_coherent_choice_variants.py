#!/usr/bin/env python3
"""Adversarial alternative choice policies for the finite coherent EPPA test.

Reverse the enumeration of actual subspaces, all source/target isomorphisms,
and all ambient general-linear automorphisms. This changes the fixed
representatives, identifications and conjugators while retaining one choice
per object and isomorphism class. Recheck every arrow and composable pair.

Finite regression only; this does not build Lean or prove the general theorem.
"""
from functools import wraps
import json
import check_banana_coherent_choices as original

EXPECTED = {
    "composable_pairs": 82697,
    "identity_checks": 135,
    "inverse_checks": 1277,
    "negative_controls": 2,
    "pairings": 17,
    "partial_isomorphisms": 1277,
    "representative_automorphisms": 491,
    "representative_classes": 81,
    "subpairs": 135,
}

def reverse_order(fn):
    @wraps(fn)
    def wrapper(*args):
        return tuple(reversed(fn(*args)))
    return wrapper

for name in ("subspaces", "linear_isos", "general_linear"):
    setattr(original, name, reverse_order(getattr(original, name)))

result = original.run()
if result != EXPECTED:
    raise AssertionError(f"Alternative coherent-choice test failed: {result}")
print(json.dumps({"choice_policy": "reverse subspace, iso and ambient orders",
                  "checks_passed": result,
                  "status": "finite regression only; not a Lean kernel check"}, indent=2))
