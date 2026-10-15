#!/usr/bin/env python3
"""Adversarial small-model check of the proposed pre-BANANA five-ary tower.

Independent of Lean. Checks:
  * all 1,022 parity-compatible child-mark requests of lengths 1..9;
  * all 1,327 compatible extension diagrams with one five-atom ambient
    stage, 1..3 source atoms and at most 3 target atoms.

For diagrams, select the globally distinct reset-letter suffix witnesses
of the Lean refinement proof (uniform depth = number of target atoms).
Verify markings, nonempty fibres, complete partition and commutation. This is NOT a proof of the infinite limit.
"""
from itertools import product


def parity(bits):
    return sum(bits) % 2


def descendants(parent_mark, depth):
    marks = [parent_mark]
    for _ in range(depth):
        marks = [child for p in marks for child in (0, 0, 1, 1, p)]
    return marks


def allocate(parent_mark, wishes):
    assert wishes and parity(wishes) == parent_mark
    depth = 1
    while True:
        marks = descendants(parent_mark, depth)
        if marks.count(0) >= wishes.count(0) and marks.count(1) >= wishes.count(1):
            break
        depth += 1
    remaining = set(range(len(marks)))
    bins = [set() for _ in wishes]
    for b, mark in enumerate(wishes):
        leaf = next(i for i in sorted(remaining) if marks[i] == mark)
        bins[b].add(leaf)
        remaining.remove(leaf)
    bins[0].update(remaining)
    assert all(bins)
    assert len(set().union(*bins)) == len(marks)
    assert sum(map(len, bins)) == len(marks)
    assert all(parity(marks[i] for i in bin_) == bit
               for bin_, bit in zip(bins, wishes))
    return depth


def surjective(labels, count):
    return len(set(labels)) == count


def check_diagram(ambient_to_source, n_source, target_to_source, n_target, target_marks):
    """Extend an embedding A -> ambient through A -> B to a deeper stage."""
    ambient_marks = (0, 0, 1, 1, 0)
    depth = n_target  # A uniform bound independent of the old ambient embedding.
    descendant_marks = {i: descendants(ambient_marks[i], depth) for i in range(5)}
    bins = [set() for _ in range(n_target)]
    for a in range(n_source):
        leaves = {(i, j)
                  for i in range(5) if ambient_to_source[i] == a
                  for j in range(5 ** depth)}
        remaining = set(leaves)
        target_atoms = [b for b in range(n_target) if target_to_source[b] == a]
        assert target_atoms
        # Use the *same* explicit witness family as the Lean proof:
        # a suffix of length |B| with 4 everywhere, except at the
        # target atom's globally unique position, where 0 or 2
        # resets the marking. All witnesses lie below one selected
        # old parent in the appropriate source fibre.
        parent = min(i for i in range(5) if ambient_to_source[i] == a)
        for b in target_atoms:
            suffix = [4] * depth
            suffix[b] = 0 if target_marks[b] == 0 else 2
            index = 0
            for letter in suffix:
                index = 5 * index + letter
            chosen = (parent, index)
            assert chosen in remaining
            assert descendant_marks[parent][index] == target_marks[b]
            bins[b].add(chosen)
            remaining.remove(chosen)
        bins[target_atoms[0]].update(remaining)

        # Commutativity over a: the union of target bins is exactly the
        # inverse image of the ambient image of the source atom.
        assert set().union(*(bins[b] for b in target_atoms)) == leaves

    universe = {(i, j) for i in range(5) for j in range(5 ** depth)}
    assert all(bins)
    assert sum(map(len, bins)) == len(universe)
    assert set().union(*bins) == universe
    assert all(parity(descendant_marks[i][j] for i, j in bins[b]) == target_marks[b]
               for b in range(n_target))


def word_mark(word):
    """The exact recursive finite-word marking formalised in Lean."""
    value = 0
    for letter in word:
        value = (0 if letter in (0, 1) else
                 1 if letter in (2, 3) else value)
    return value


def check_word_levels():
    """Independently check prefix fibres and even total marking."""
    for n in range(5):
        words = list(product(range(5), repeat=n))
        marks = [word_mark(w) for w in words]
        assert parity(marks) == 0
        assert sum(marks) == (5 ** n - 1) // 2
        for w in words:
            assert parity(word_mark(w + (c,)) for c in range(5)) == word_mark(w)
    return 5


def main():
    word_levels = check_word_levels()
    split_checks = 0
    maximum_depth = 0
    for parent in (0, 1):
        for n in range(1, 10):
            for wishes in product((0, 1), repeat=n):
                if parity(wishes) != parent:
                    continue
                maximum_depth = max(maximum_depth, allocate(parent, wishes))
                split_checks += 1
    assert split_checks == 1022
    assert maximum_depth == 2

    diagram_checks = 0
    for n_source in (1, 2, 3):
        for ambient_to_source in product(range(n_source), repeat=5):
            if not surjective(ambient_to_source, n_source):
                continue
            source_marks = [
                parity((0, 0, 1, 1, 0)[i]
                       for i in range(5) if ambient_to_source[i] == a)
                for a in range(n_source)
            ]
            for n_target in range(n_source, 4):
                for target_to_source in product(range(n_source), repeat=n_target):
                    if not surjective(target_to_source, n_source):
                        continue
                    for target_marks in product((0, 1), repeat=n_target):
                        if any(
                            parity(target_marks[b] for b in range(n_target)
                                   if target_to_source[b] == a) != source_marks[a]
                            for a in range(n_source)
                        ):
                            continue
                        check_diagram(ambient_to_source, n_source,
                                      target_to_source, n_target, target_marks)
                        diagram_checks += 1
    assert diagram_checks == 1327
    print(f"PASS: {word_levels} complete five-ary word levels")
    print(f"PASS: {split_checks} child-mark splits (maximal depth {maximum_depth})")
    print(f"PASS: {diagram_checks} finite embedding extension diagrams")


if __name__ == "__main__":
    main()
