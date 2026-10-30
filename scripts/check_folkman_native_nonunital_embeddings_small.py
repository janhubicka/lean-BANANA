#!/usr/bin/env python3
"""Exhaustive finite check of non-unital Folkman pairing transport.

A source-to-target Boolean-ring embedding is a partial owner map on
ambient atoms: each source atom owns a nonempty fibre; unowned ambient
atoms are allowed.  For every such pair of maps and every ambient
atom pairing, the source matrix is induced from the owner fibres.
Test that the resulting embedding preserves the original pairing
on ALL ring elements, not merely pairs of atoms.  Check the two
ring operations and injectivity, including both zero-ring sorts.

This is an adversarial finite regression, not a Lean proof.
"""
from collections import Counter
from itertools import product


def owners(source_count, target_count):
    for values in product(range(-1, source_count), repeat=target_count):
        if all(i in values for i in range(source_count)):
            yield values


def image(bits, owner):
    return sum(1 << t for t, a in enumerate(owner)
               if a >= 0 and bits & (1 << a))


def pairing(matrix, right_count, left, right):
    ans = 0
    i = 0
    while left:
        if left & 1:
            for j in range(right_count):
                if right & (1 << j):
                    ans ^= (matrix >> (i * right_count + j)) & 1
        left >>= 1
        i += 1
    return ans


def main():
    counts = Counter()
    unused = False
    for source_l in range(3):
        for source_r in range(3):
            for target_l in range(source_l, 4):
                for target_r in range(source_r, 4):
                    for owner_l in owners(source_l, target_l):
                        left_images = [
                            image(x, owner_l) for x in range(1 << source_l)
                        ]
                        assert len(set(left_images)) == len(left_images)
                        assert left_images[0] == 0
                        for x in range(1 << source_l):
                            for y in range(1 << source_l):
                                assert left_images[x ^ y] == (
                                    left_images[x] ^ left_images[y])
                                assert left_images[x & y] == (
                                    left_images[x] & left_images[y])
                                counts["ring_map_checks"] += 1
                        for owner_r in owners(source_r, target_r):
                            right_images = [
                                image(y, owner_r) for y in range(1 << source_r)
                            ]
                            assert len(set(right_images)) == len(right_images)
                            assert right_images[0] == 0
                            for y in range(1 << source_r):
                                for z in range(1 << source_r):
                                    assert right_images[y ^ z] == (
                                        right_images[y] ^ right_images[z])
                                    assert right_images[y & z] == (
                                        right_images[y] & right_images[z])
                                    counts["ring_map_checks"] += 1
                            for ambient_matrix in range(1 << (target_l * target_r)):
                                source_matrix = 0
                                for i in range(source_l):
                                    for j in range(source_r):
                                        v = pairing(ambient_matrix, target_r,
                                                    left_images[1 << i],
                                                    right_images[1 << j])
                                        source_matrix |= v << (i * source_r + j)
                                for x in range(1 << source_l):
                                    for y in range(1 << source_r):
                                        assert pairing(source_matrix, source_r,
                                                       x, y) == pairing(
                                            ambient_matrix, target_r,
                                            left_images[x], right_images[y])
                                        counts["pairing_checks"] += 1
                                unused |= -1 in owner_l or -1 in owner_r
                                counts["embeddings"] += 1
    assert unused
    assert counts["embeddings"] == 221537
    assert counts["pairing_checks"] == 2160253
    assert counts["ring_map_checks"] == 10336
    for k, v in counts.items():
        print(f"{k}: {v:,}")
    print("PASS; includes zero rings and unowned target atoms")


if __name__ == "__main__":
    main()
