#!/usr/bin/env python3
"""Independent finite referee for Track D's unindexed coherent-groupoid descent.

The test uses GL(3,2) acting on all genuine 0-, 1-, and 2-dimensional
subspaces of F_2^3. Each isomorphism class chooses one representative,
one identification and one conjugator per object. The left/right
composition convention matches the transported action of a subgroup.

It checks all arrows, inverses and composable pairs in each class, with
two distinct systems of objectwise conjugators and noncanonical class labels.
This is a finite regression, NOT a Lean kernel check or a test of the
BANANA perfect pairing's bilinear preservation.
"""
from __future__ import annotations

from itertools import product
from collections import Counter
import json


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def image(cols: tuple[int, ...], x: int) -> int:
    value = 0
    for i, col in enumerate(cols):
        if x & (1 << i):
            value ^= col
    return value


def generated(*gens: int) -> tuple[int, ...]:
    out = {0}
    for v in gens:
        out |= {x ^ v for x in tuple(out)}
    return tuple(sorted(out))


def linear_group(n: int) -> tuple[tuple[int, ...], ...]:
    out = []
    for cols in product(range(1 << n), repeat=n):
        if len(generated(*cols)) == (1 << n):
            out.append(tuple(image(cols, x) for x in range(1 << n)))
    return tuple(out)


def compose(f: tuple[int, ...], g: tuple[int, ...]) -> tuple[int, ...]:
    """f*g means first g, then f."""
    return tuple(f[g[x]] for x in range(len(g)))


def inverse(f: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(f)
    for x, y in enumerate(f):
        out[y] = x
    return tuple(out)


def check() -> dict[str, int]:
    G3 = linear_group(3)
    G2 = linear_group(2)
    identity = tuple(range(8))
    require(len(G3) == 168, "incorrect GL(3,2) cardinality")
    require(len(G2) == 6, "incorrect GL(2,2) cardinality")
    counts: Counter[str] = Counter()
    for dim in (0, 1, 2):
        subspaces = sorted({generated(*generators)
            for generators in product(range(8), repeat=dim)
            if len(generated(*generators)) == (1 << dim)})
        require(len(subspaces) == (1 if dim == 0 else 7),
                f"incorrect number of subspaces, dimension={dim}")
        representative = generated(*(1 << i for i in range(dim)))
        rho = G2 if dim == 2 else (tuple(range(1 << dim)),)

        def extend(a: tuple[int, ...]) -> tuple[int, ...]:
            def f(x: int) -> int:
                low = x & ((1 << dim) - 1)
                return a[low] | (x & (7 ^ ((1 << dim) - 1)))
            return tuple(f(x) for x in range(8))

        for h in rho:
            require(extend(h) in G3, "representative map not invertible")
        for choice_index in (0, -1):
            conjugators = {}
            for U in subspaces:
                candidates = [g for g in G3 if tuple(sorted(g[x] for x in representative)) == U]
                require(len(candidates) > 1, "object admits no alternative conjugator")
                conjugators[U] = candidates[choice_index]
            # The quotient's class label is arbitrary: changing it must
            # not affect the descended map on an actual arrow.
            reference_actions = None
            for class_label in (0, 23, -117):
                class_of = {U: class_label for U in subspaces}
                indexed_actions = {
                    (class_label, U, V, a): compose(
                        compose(conjugators[V], extend(a)), inverse(conjugators[U]))
                    for U in subspaces for V in subspaces for a in rho
                }

                def theta(U: tuple[int, ...], V: tuple[int, ...], a: tuple[int, ...]) -> tuple[int, ...]:
                    require(class_of[U] == class_of[V], "mismatched quotient class")
                    return indexed_actions[class_of[U], U, V, a]

                action_values = {(U, V, a): theta(U, V, a)
                                 for U in subspaces for V in subspaces for a in rho}
                if reference_actions is None:
                    reference_actions = action_values
                else:
                    require(action_values == reference_actions,
                            "changing quotient labels altered descended action")
                counts["reindexing_comparisons"] += len(action_values)

                for U in subspaces:
                    require(theta(U, U, tuple(range(1 << dim))) == identity,
                            "identity not preserved")
                    counts["identity"] += 1
                    for V in subspaces:
                        for a in rho:
                            t = theta(U, V, a)
                            require(t in G3, "not an ambient group element")
                            require(tuple(sorted(t[x] for x in U)) == V,
                                    "partial isomorphism not extended")
                            require(theta(V, U, inverse(a)) == inverse(t),
                                    "inverse law fails")
                            counts["arrows"] += 1
                            counts["inverse"] += 1
                            for W in subspaces:
                                for b in rho:
                                    qp = compose(b, a)
                                    actual = compose(theta(V, W, b), t)
                                    require(actual == theta(U, W, qp),
                                            "composition fails after class-index descent")
                                    counts["composable_pairs"] += 1
                counts["label_assignments"] += 1

            # This deliberately incorrect formula drops the inverse of
            # the source conjugator. It must be detected by the checker.
            wrong_identity = any(
                compose(conjugators[U], conjugators[U]) != identity
                for U in subspaces)
            if wrong_identity:
                counts["wrong_formula_rejected"] += 1
        counts["classes"] += 1

    require(counts["wrong_formula_rejected"] > 0, "mutation control not triggered")
    return dict(sorted(counts.items()))


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
