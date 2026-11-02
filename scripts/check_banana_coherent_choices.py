#!/usr/bin/env python3
"""Construct and exhaustively test coherent EPPA choices in small BANANAs.

For EVERY binary pairing with l+r <= 3, use ONE perfect witness of side
dimension l+r, ONE representative per actual isomorphism class of subpairs,
ONE representative identification and ambient conjugator per subpair, and
ONE completion homomorphism per representative. Check every arrow, inverse,
identity and composable pair. This is a finite regression, not a Lean proof.

Only Python's standard library is required. The zero-dimensional vector
space has one vector (0); it is not an empty sort.
"""
from __future__ import annotations

from collections import defaultdict
from functools import lru_cache
from itertools import product
import json
from typing import Iterable

Perm = tuple[int, ...]
Space = tuple[int, ...]


def check(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def compose(f: Perm, g: Perm) -> Perm:
    """f * g: first apply g, then f."""
    return tuple(f[g[x]] for x in range(len(g)))


def inverse(f: Perm) -> Perm:
    result = [0] * len(f)
    for x, y in enumerate(f):
        result[y] = x
    return tuple(result)


def lin(columns: tuple[int, ...], x: int) -> int:
    result = 0
    for i, v in enumerate(columns):
        if (x >> i) & 1:
            result ^= v
    return result


def span(generators: Iterable[int]) -> Space:
    result = {0}
    for v in generators:
        result |= {x ^ v for x in tuple(result)}
    return tuple(sorted(result))


@lru_cache(None)
def basis(space: Space) -> tuple[int, ...]:
    result: list[int] = []
    seen = (0,)
    for v in space:
        if v not in seen:
            result.append(v)
            seen = span(result)
    check(seen == space, "basis does not span the supplied subspace")
    return tuple(result)


@lru_cache(None)
def subspaces(n: int) -> tuple[Space, ...]:
    result = {(0,)}
    for v in range(1, 1 << n):
        result |= {span(s + (v,)) for s in tuple(result)}
    return tuple(sorted(result, key=lambda s: (len(s), s)))


@lru_cache(None)
def linear_isos(source: Space, target: Space) -> tuple[Perm, ...]:
    """Values on the sorted source carrier, NOT an ambient permutation."""
    if len(source) != len(target):
        return ()
    bs = basis(source)
    coordinates = {lin(bs, x): x for x in range(1 << len(bs))}
    result = []
    for images in product(target, repeat=len(bs)):
        if span(images) == target:
            result.append(tuple(lin(images, coordinates[x]) for x in source))
    return tuple(result)


def dot(x: int, y: int) -> int:
    return (x & y).bit_count() & 1


@lru_cache(None)
def contragredient(f: Perm) -> Perm:
    n = len(f).bit_length() - 1
    finv = inverse(f)
    return tuple(sum(dot(finv[1 << i], y) << i for i in range(n))
                 for y in range(1 << n))


@lru_cache(None)
def general_linear(n: int) -> tuple[Perm, ...]:
    space = tuple(range(1 << n))
    result = linear_isos(space, space)
    for f in result:
        r = contragredient(f)
        check(all(dot(f[x], r[y]) == dot(x, y) for x in space for y in space),
              "contragredient does not preserve the perfect pairing")
    return result


def run() -> dict[str, int]:
    counts: defaultdict[str, int] = defaultdict(int)
    for n in range(4):
        for l in range(n + 1):
            r = n - l
            ambient = general_linear(n)
            ident = tuple(range(1 << n))
            for rows in product(range(1 << r), repeat=l):
                counts["pairings"] += 1

                def beta(x: int, y: int) -> int:
                    return dot(x, sum(dot(row, y) << i for i, row in enumerate(rows)))

                def jl(x: int) -> int:
                    return x

                def jr(y: int) -> int:
                    return sum(dot(row, y) << i for i, row in enumerate(rows)) | (y << l)

                check(all(dot(jl(x), jr(y)) == beta(x, y)
                          for x in range(1 << l) for y in range(1 << r)),
                      "original structure is not embedded in the common witness")
                objects = tuple(product(subspaces(l), subspaces(r)))
                counts["subpairs"] += len(objects)
                arrows = {}
                for u, (ul, ur) in enumerate(objects):
                    for v, (vl, vr) in enumerate(objects):
                        if len(ul) != len(vl) or len(ur) != len(vr):
                            arrows[u, v] = ()
                            continue
                        arrows[u, v] = tuple(
                            (fl, fr) for fl in linear_isos(ul, vl)
                            for fr in linear_isos(ur, vr)
                            if all(beta(fl[ix], fr[iy]) == beta(x, y)
                                   for ix, x in enumerate(ul) for iy, y in enumerate(ur)))

                representatives = {}
                coordinates = {}
                conjugators = {}
                homs = {}
                for u, (ul, ur) in enumerate(objects):
                    rep = next(v for v in range(u + 1) if arrows[v, u])
                    representatives[u] = rep
                    rl, rr = objects[rep]
                    i_l, i_r = arrows[rep, u][0]
                    coordinates[u] = (dict(zip(rl, i_l)), dict(zip(rr, i_r)))
                    conjugators[u] = next(t for t in ambient
                        if all(t[jl(x)] == jl(i_l[ix]) for ix, x in enumerate(rl))
                        and all(contragredient(t)[jr(y)] == jr(i_r[iy])
                                for iy, y in enumerate(rr)))
                    if rep in homs:
                        continue
                    counts["representative_classes"] += 1
                    bl, br = basis(rl), basis(rr)
                    a, b = len(bl), len(br)
                    m = a + b
                    check(m <= n, "representative completion exceeds witness dimension")

                    # Standard perfect completion of the representative, embedded
                    # into the first m coordinates of the SAME n-dimensional witness.
                    def rep_right(y: int) -> int:
                        return sum(beta(x, lin(br, y)) << i for i, x in enumerate(bl)) | (y << a)

                    alpha = next(t for t in ambient
                        if all(t[x] == jl(lin(bl, x)) for x in range(1 << a))
                        and all(contragredient(t)[rep_right(y)] == jr(lin(br, y))
                                for y in range(1 << b)))
                    inv_alpha = inverse(alpha)
                    left_coord = {lin(bl, x): x for x in range(1 << a)}
                    right_coord = {lin(br, y): y for y in range(1 << b)}
                    rl_index, rr_index = {x: i for i, x in enumerate(rl)}, {y: i for i, y in enumerate(rr)}
                    hom = {}
                    for h_l, h_r in arrows[rep, rep]:
                        f = tuple(left_coord[h_l[rl_index[lin(bl, x)]]]
                                  for x in range(1 << a))
                        g = tuple(right_coord[h_r[rr_index[lin(br, y)]]]
                                  for y in range(1 << b))
                        cg = contragredient(g)
                        block = tuple(f[z & ((1 << a) - 1)] |
                                      (cg[(z >> a) & ((1 << b) - 1)] << a) |
                                      ((z >> m) << m) for z in range(1 << n))
                        lifted = compose(compose(alpha, block), inv_alpha)
                        check(lifted in ambient, "completion action is not an ambient automorphism")
                        check(all(lifted[jl(x)] == jl(h_l[ix]) for ix, x in enumerate(rl))
                              and all(contragredient(lifted)[jr(y)] == jr(h_r[iy])
                                      for iy, y in enumerate(rr)),
                              "aligned completion action does not extend its automorphism")
                        hom[h_l, h_r] = lifted
                        counts["representative_automorphisms"] += 1
                    homs[rep] = hom

                # Store ONE extension for each arrow, using only the fixed choices.
                theta = {}
                for (u, v), maps in arrows.items():
                    if not maps:
                        continue
                    rep = representatives[u]
                    check(rep == representatives[v], "isomorphic subpairs received different representatives")
                    rl, rr = objects[rep]
                    iul, iur = coordinates[u]
                    ivl, ivr = coordinates[v]
                    inv_ivl, inv_ivr = {y: x for x, y in ivl.items()}, {y: x for x, y in ivr.items()}
                    ul, ur = objects[u]
                    for pl, pr in maps:
                        p_l, p_r = dict(zip(ul, pl)), dict(zip(ur, pr))
                        h_l = tuple(inv_ivl[p_l[iul[x]]] for x in rl)
                        h_r = tuple(inv_ivr[p_r[iur[y]]] for y in rr)
                        h = homs[rep][h_l, h_r]
                        t = compose(compose(conjugators[v], h), inverse(conjugators[u]))
                        check(t in ambient, "transport is not an ambient linear automorphism")
                        tr = contragredient(t)
                        check(all(t[jl(x)] == jl(pl[ix]) for ix, x in enumerate(ul))
                              and all(tr[jr(y)] == jr(pr[iy]) for iy, y in enumerate(ur)),
                              "transport fails to extend an actual partial isomorphism")
                        theta[u, v, pl, pr] = t
                        counts["partial_isomorphisms"] += 1

                for u, (ul, ur) in enumerate(objects):
                    check(theta[u, u, ul, ur] == ident and
                          contragredient(theta[u, u, ul, ur]) == ident,
                          "identity arrow gets a nonidentity extension")
                    counts["identity_checks"] += 1
                for (u, v), maps in arrows.items():
                    ul, ur = objects[u]
                    vl, vr = objects[v]
                    for pl, pr in maps:
                        tp = theta[u, v, pl, pr]
                        il, ir = dict(zip(pl, ul)), dict(zip(pr, ur))
                        inv_l, inv_r = tuple(il[x] for x in vl), tuple(ir[y] for y in vr)
                        check(theta[v, u, inv_l, inv_r] == inverse(tp) and
                              contragredient(theta[v, u, inv_l, inv_r]) ==
                              inverse(contragredient(tp)), "inverse coherence failed")
                        counts["inverse_checks"] += 1
                        for w in range(len(objects)):
                            for ql, qr in arrows[v, w]:
                                q_l, q_r = dict(zip(vl, ql)), dict(zip(vr, qr))
                                qp_l, qp_r = tuple(q_l[x] for x in pl), tuple(q_r[y] for y in pr)
                                tq = theta[v, w, ql, qr]
                                tqp = theta[u, w, qp_l, qp_r]
                                check(compose(tq, tp) == tqp, "left composition coherence failed")
                                check(compose(contragredient(tq), contragredient(tp)) ==
                                      contragredient(tqp), "right composition coherence failed")
                                counts["composable_pairs"] += 1

    # Two negative controls: an arbitrary extension of an identity need not
    # be the identity, and multiplication order is visible in GL(2,2).
    p, q = (0, 1, 3, 2), (0, 3, 2, 1)
    check(p in general_linear(2) and q in general_linear(2), "invalid negative-control maps")
    check(p[0] == 0 and p != tuple(range(4)), "identity extension negative control failed")
    check(compose(p, q) != compose(q, p), "composition-order negative control failed")
    counts["negative_controls"] = 2
    return dict(sorted(counts.items()))


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
