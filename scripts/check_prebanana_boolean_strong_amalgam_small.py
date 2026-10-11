#!/usr/bin/env python3
"""Exhaustive finite Boolean-algebra regression for pre-BANANA strong AP.

The star-marked compatible atom grid gives embeddings B,C -> D.
Test all allowed source atom markings and surjective atom-partition
maps with 1..3 source atoms and at most four atoms on either side.
For every resulting pair of compatible marked structures, check
zero total marking, both marked-fibre identities, injectivity of
Boolean-element embeddings, preservation of parity and of the
Boolean operations (including complementation), commutativity of
the diagram, and exact intersection for *all* Boolean elements.

This adversarial finite-model test is not a Lean proof, and does
not establish the theorem for arbitrary finite dimensions.
"""
from collections import Counter, defaultdict
from itertools import product


def even_marks(n):
    return [m for m in product((0, 1), repeat=n) if sum(m) % 2 == 0]


def surjections(m, n):
    return [f for f in product(range(n), repeat=m) if len(set(f)) == n]


def source_marks(f, marks, n):
    return tuple(sum(marks[b] for b in range(len(f)) if f[b] == a) % 2
                 for a in range(n))


def check_diagram(na, nb, nc, f, g, mb, mc):
    grid = [(b, c) for b in range(nb) for c in range(nc) if f[b] == g[c]]
    nd = len(grid)
    full_d = (1 << nd) - 1
    lookup = {pair: i for i, pair in enumerate(grid)}
    md = [0] * nd
    for a in range(na):
        bs = [b for b in range(nb) if f[b] == a]
        cs = [c for c in range(nc) if g[c] == a]
        b0, c0 = bs[-1], cs[-1]
        for b in bs:
            for c in cs:
                md[lookup[b, c]] = (
                    0 if b != b0 and c != c0 else
                    mb[b] if b != b0 else
                    mc[c] if c != c0 else
                    (mb[b0] + sum(mc[x] for x in cs[:-1])) % 2
                )
    assert sum(md) % 2 == 0
    images_b = [sum(1 << i for i, (b, _) in enumerate(grid) if s >> b & 1)
                for s in range(1 << nb)]
    images_c = [sum(1 << i for i, (_, c) in enumerate(grid) if s >> c & 1)
                for s in range(1 << nc)]
    assert len(set(images_b)) == (1 << nb)
    assert len(set(images_c)) == (1 << nc)
    tested = Counter()
    for images, marks in ((images_b, mb), (images_c, mc)):
        n = len(marks)
        full = (1 << n) - 1
        for s in range(1 << n):
            assert images[full ^ s] == (full_d ^ images[s])
            parity_old = sum(marks[i] for i in range(n) if s >> i & 1) % 2
            parity_new = sum(md[i] for i in range(nd)
                             if images[s] >> i & 1) % 2
            assert parity_old == parity_new
            for t in range(1 << n):
                assert images[s | t] == images[s] | images[t]
                assert images[s & t] == images[s] & images[t]
        tested["boolean_elements"] += 1 << n
    common = set()
    for sa in range(1 << na):
        sb = sum(1 << b for b in range(nb) if sa >> f[b] & 1)
        sc = sum(1 << c for c in range(nc) if sa >> g[c] & 1)
        assert images_b[sb] == images_c[sc]
        common.add((sb, sc))
        tested["commuting_source_elements"] += 1
    for sb in range(1 << nb):
        for sc in range(1 << nc):
            if images_b[sb] == images_c[sc]:
                assert (sb, sc) in common
                tested["common_image_equalities"] += 1
    tested["compatible_diagrams"] += 1
    return tested


def main():
    total = Counter()
    for na in range(1, 4):
        for nb in range(na, 5):
            for nc in range(na, 5):
                left = defaultdict(list)
                right = defaultdict(list)
                for f in surjections(nb, na):
                    for mb in even_marks(nb):
                        left[source_marks(f, mb, na)].append((f, mb))
                for g in surjections(nc, na):
                    for mc in even_marks(nc):
                        right[source_marks(g, mc, na)].append((g, mc))
                for marks_a in even_marks(na):
                    for f, mb in left[marks_a]:
                        for g, mc in right[marks_a]:
                            total.update(check_diagram(na, nb, nc, f, g, mb, mc))
    print("pre-BANANA finite Boolean strong AP: PASS")
    for name in ("compatible_diagrams", "boolean_elements",
                 "commuting_source_elements", "common_image_equalities"):
        print(f"  {name}: {total[name]:,}")
    assert total["compatible_diagrams"] == 34361
    assert total["common_image_equalities"] == 234338


if __name__ == "__main__":
    main()
