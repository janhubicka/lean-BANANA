#!/usr/bin/env python3
"""Adversarial alternative choice policies for finite coherent BANANA.

Reverse the enumeration of subspaces, all source/target isomorphisms and
ambient general-linear automorphisms. This changes the fixed representatives,
identifications and conjugators, whilst keeping one choice per object/class.
By default, check all cases of total dimension at most three. --mixed4 checks
all 32 pairings with nonzero left and right dimensions totalling four.

Finite testing only, not Lean kernel verification or independent refereeing.
"""
from functools import wraps
import argparse
import json
import check_banana_coherent_choices as original

EXPECTED_SMALL = {
    'composable_pairs': 82697,
    'identity_checks': 135,
    'inverse_checks': 1277,
    'negative_controls': 2,
    'pairings': 17,
    'partial_isomorphisms': 1277,
    'representative_automorphisms': 491,
    'representative_classes': 81,
    'subpairs': 135,
}

EXPECTED_MIXED4 = {
    'composable_pairs': 770480,
    'identity_checks': 912,
    'inverse_checks': 12908,
    'negative_controls': 2,
    'pairings': 32,
    'partial_isomorphisms': 12908,
    'representative_automorphisms': 4217,
    'representative_classes': 333,
    'subpairs': 912,
}


def reverse_order(fn):
    @wraps(fn)
    def wrapper(*args):
        return tuple(reversed(fn(*args)))
    return wrapper


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mixed4', action='store_true',
                        help='check all mixed-sort pairings of dimension four')
    args = parser.parse_args()
    for name in ('subspaces', 'linear_isos', 'general_linear'):
        setattr(original, name, reverse_order(getattr(original, name)))
    cases = {(4, 1), (4, 2), (4, 3)} if args.mixed4 else None
    expected = EXPECTED_MIXED4 if args.mixed4 else EXPECTED_SMALL
    result = original.run(cases=cases)
    if result != expected:
        raise AssertionError(f'Alternative-choice regression failed: {result}')
    print(json.dumps({'choice_policy': 'reverse subspace/iso/ambient orders',
                      'case_scope': 'mixed dimension four' if args.mixed4 else 'total dimension <= 3',
                      'checks_passed': result,
                      'verified': 'finite regression only, not Lean kernel'}, indent=2))


if __name__ == '__main__':
    main()
