#!/usr/bin/env python3
"""Independent finite check of actual-subpair -> coordinate functor.

All binary pairings with l+r<=3 and all actual pairing-preserving two-sort
isomorphisms are examined. A noncanonical, object-specific coordinate basis
is fixed ONCE for each actual subpair. Verify identity, inverses, full
composition and restricted pairing under coordinate transport. No Lean claims.
"""
from collections import defaultdict
from itertools import permutations, product
import json
import sys


def check(predicate, description):
    """Runtime guard, also active under python -O."""
    if not predicate:
        raise AssertionError(description)


def parity(x):
    return x.bit_count() & 1


def span(B):
    s = {0}
    for v in B:
        s |= {v ^ x for x in tuple(s)}
    return frozenset(s)


def all_subspaces(n):
    s = {frozenset({0})}
    for v in range(1, 1 << n):
        s |= {span(u | {v}) for u in tuple(s)}
    return tuple(sorted(s, key=lambda u: (len(u), tuple(sorted(u)))))


def bases(S):
    d = len(S).bit_length() - 1
    return tuple(b for b in permutations(sorted(S - {0}), d) if span(b) == S)


def expand(B, x):
    y = 0
    for i, v in enumerate(B):
        if x >> i & 1:
            y ^= v
    return y


def coordinate(B, x):
    return next(t for t in range(1 << len(B)) if expand(B, t) == x)


def pair(rows, x, y):
    return parity(sum(parity(row & y) << i for i, row in enumerate(rows)) & x)


def linear_maps(S, T):
    if len(S) != len(T):
        return ()
    src = bases(S)[0]
    return tuple(tuple(expand(images, coordinate(src, x)) for x in sorted(S))
                 for images in bases(T))


def compose(f, g):
    return tuple(f[g[x]] for x in range(len(g)))


def inverse(f):
    ans = [0] * len(f)
    for x, y in enumerate(f):
        ans[y] = x
    return tuple(ans)


def run():
    counts = defaultdict(int)
    for n in range(4):
        for l in range(n + 1):
            r = n - l
            for rows in product(range(1 << r), repeat=l):
                counts['pairings'] += 1
                objs = tuple(product(all_subspaces(l), all_subspaces(r)))
                coords = {}
                for idx, (left, right) in enumerate(objs):
                    # Deliberately choose different bases for the same subspace
                    # in different two-sorted objects, to test cancellation.
                    BL = bases(left)
                    BR = bases(right)
                    bl = BL[(idx + 1) % len(BL)]
                    br = BR[(3 * idx + 2) % len(BR)]
                    coords[idx] = (bl, br)
                    counts['objects'] += 1
                arrows = {}
                for u, (ul, ur) in enumerate(objs):
                    buL, buR = coords[u]
                    for v, (vl, vr) in enumerate(objs):
                        bvL, bvR = coords[v]
                        aa = []
                        for fl in linear_maps(ul, vl):
                            flmap = dict(zip(sorted(ul), fl))
                            for fr in linear_maps(ur, vr):
                                frmap = dict(zip(sorted(ur), fr))
                                if not all(pair(rows, flmap[x], frmap[y]) == pair(rows, x, y)
                                           for x in ul for y in ur):
                                    continue
                                cl = tuple(coordinate(bvL, flmap[expand(buL, t)])
                                           for t in range(1 << len(buL)))
                                cr = tuple(coordinate(bvR, frmap[expand(buR, t)])
                                           for t in range(1 << len(buR)))
                                check(len(set(cl)) == len(cl) and len(set(cr)) == len(cr),
                                      "coordinate map is not bijective")
                                check(all(pair(rows, expand(bvL, cl[x]), expand(bvR, cr[y])) ==
                                          pair(rows, expand(buL, x), expand(buR, y))
                                          for x in range(len(cl)) for y in range(len(cr))),
                                      "coordinate map fails pairing preservation")
                                aa.append((fl, fr, cl, cr))
                        arrows[u, v] = aa
                        counts['arrows'] += len(aa)
                for u, (ul, ur) in enumerate(objs):
                    ids = (tuple(sorted(ul)), tuple(sorted(ur)))
                    hits = [a for a in arrows[u, u] if (a[0], a[1]) == ids]
                    check(len(hits) == 1, "actual identity arrow not unique")
                    check(hits[0][2] == tuple(range(len(hits[0][2]))),
                          "coordinate functor fails left identity")
                    check(hits[0][3] == tuple(range(len(hits[0][3]))),
                          "coordinate functor fails right identity")
                    counts['identities'] += 1
                for (u, v), ps in arrows.items():
                    if not ps:
                        continue
                    ul, ur = objs[u]
                    vl, vr = objs[v]
                    buL, buR = coords[u]
                    bvL, bvR = coords[v]
                    for fl, fr, cl, cr in ps:
                        invl = dict(zip(fl, sorted(ul)))
                        invr = dict(zip(fr, sorted(ur)))
                        back = (tuple(invl[x] for x in sorted(vl)),
                                tuple(invr[y] for y in sorted(vr)))
                        backcode = next((al, ar) for bl, br, al, ar in arrows[v, u]
                                        if (bl, br) == back)
                        check(backcode == (inverse(cl), inverse(cr)),
                              "coordinate functor fails inverse law")
                        counts['inverses'] += 1
                        for w in range(len(objs)):
                            for ql, qr, cql, cqr in arrows[v, w]:
                                qmL = dict(zip(sorted(vl), ql))
                                qmR = dict(zip(sorted(vr), qr))
                                compmap = (tuple(qmL[x] for x in fl),
                                           tuple(qmR[y] for y in fr))
                                composedcode = next((al, ar) for bl, br, al, ar in arrows[u, w]
                                                    if (bl, br) == compmap)
                                check(composedcode == (compose(cql, cl), compose(cqr, cr)),
                                      "coordinate functor fails composition law")
                                counts['compositions'] += 1
    # Explicit mutation: code the identity map from the standard basis to
    # a switched target basis in the middle, then compose with another
    # identity coded in the standard basis. Different bases for the SAME
    # middle object violate the functoriality equation.
    standard, changed = (1, 2), (2, 1)
    wrong_p = tuple(coordinate(changed, expand(standard, x)) for x in range(4))
    q = tuple(coordinate(standard, expand(standard, x)) for x in range(4))
    actual_composite = tuple(range(4))
    check(compose(q, wrong_p) != actual_composite,
          "inconsistent midpoint basis did not falsify composition")
    counts['bad_midpoint_basis_control'] = 1
    return dict(sorted(counts.items()))


if __name__ == '__main__':
    if '--probe-guard' in sys.argv:
        # Intentionally fail. The process must exit nonzero with and without -O.
        check(False, 'CHECK_GUARD_ACTIVE')
    print(json.dumps(run(), indent=2))
