#!/usr/bin/env python3
"""Full coherent-extension regression in total dimension 4, mixed sorts.

Checks all 32 pairings with (left,right) dimensions (1,3), (2,2), (3,1).
It tests ONE coherent choice assignment for every actual partial
isomorphism of every pairing, identities, inverses, both embedding
restrictions and all composable pairs. The two one-sided cases (0,4)
and (4,0) have much larger composition counts and are not included.

This is a finite test, NOT a Lean kernel proof or a mathematical
replacement for an independent referee.
"""
import json
import check_banana_coherent_choices as source

EXPECTED = {
    "composable_pairs": 770480,
    "identity_checks": 912,
    "inverse_checks": 12908,
    "negative_controls": 2,
    "pairings": 32,
    "partial_isomorphisms": 12908,
    "representative_automorphisms": 4217,
    "representative_classes": 333,
    "subpairs": 912,
}

result = source.run(cases={(4, 1), (4, 2), (4, 3)})
if result != EXPECTED:
    raise AssertionError(f"Dimension-four coherent extension regression failed: {result}")
print(json.dumps({"scope": "total dimension 4, both sorts nonzero",
                  "results": result,
                  "status": "finite regression only; NOT Lean verified"}, indent=2))
