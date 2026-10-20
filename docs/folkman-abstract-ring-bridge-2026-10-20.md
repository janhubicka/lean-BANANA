# Folkman–BANANA: abstract-ring strong-amalgamation bridge

**Internal mathematical audit, 20 October 2026.** This note is not part of
the frozen circulation text. It identifies the precise remaining transport
lemmas between the kernel-checked finite atom-grid amalgamation and the
paper's class of arbitrary finite Boolean rings.

## What is already verified

Merged #281 exports
`FolkmanFiniteTwoSortAtomDiagram.exists_strong_amalgam_pairing`.
Its inputs are finite sets of atoms on each of six source sorts, four
`Option`-valued atom maps with nonempty fibres over the common base,
and bilinear pairings compatible on the base. The conclusion includes:

1. an actual pairing on both finite atom-grid-plus-private-point rings;
2. additivity in each variable;
3. complete preservation of the two source pairings;
4. equality of the source images precisely in the common base.

This applies when either base sort or source sort has no atoms.
It does not itself quantify over abstract finite Boolean-ring carriers.

## Atom representation of an arbitrary finite Boolean ring

For a finite Boolean ring `R`, the (internally defined) order
`x ≤ y` iff `xy=x` makes it a finite Boolean algebra, including when
`R={0}`. Its greatest element is *not named by the ring language* and
need not be preserved by embeddings. The existing
`PrebananaFiniteBooleanRepresentation.lean` already proves the
canonical order isomorphism

`η_R : R ≃o Finset (At(R))`

for arbitrary finite Boolean algebras, with no nontriviality hypothesis.
This must be connected to the native finite Boolean-ring interface (if
represented in Lean as a ring rather than a Boolean algebra) and shown
to preserve `0`, symmetric difference and intersection.

## Reconstructing an embedding

Let `f:R→S` be an injective non-unital ring homomorphism. Transfer it
to atom subsets:

`F = η_S ∘ f ∘ η_R⁻¹ : Finset At(R) → Finset At(S)`.

The ring language preserves zero, symmetric difference and intersection.
Since `X∪Y=(X△Y)△(X∩Y)`, the map `F` also preserves union.
The new PR #282 proves that any injective finite powerset map preserving
empty, union and intersection has a partial atom-owner

`p: At(S)→Option At(R)`

whose fibres over source atoms are nonempty, and
`F(X)={b∈At(S): ∃a∈X, p(b)=some a}`.
The independently stated PR #283 derives the union hypothesis from
the *actual ring language*; neither theorem assumes `F(univ)=univ`.

The finite support `F(univ)` consists precisely of target atoms with
a non-`none` owner. The remaining atoms are private to the target.
This is not a defect in the proof: it is the defining difference
between Folkman–BANANA and pre-BANANA embeddings.

## From abstract diagrams to the checked atom amalgam

Given the two embeddings `A→B` and `A→C` on both ring sorts, apply
the partial-owner theorem to all four maps to obtain the
`FolkmanFiniteTwoSortAtomDiagram` datum. Transfer the original
source pairings by `η_R⁻¹`; their bilinearity follows from preservation
of symmetric difference. Their restrictions agree on the common
base because both source embeddings preserve the relation.

Apply merged #281. Its destination is already a finite powerset
Boolean ring on the constructed atom grid (not an abstract vector
space with unspecified multiplication). Compose the source maps with
their atom-code isomorphisms to obtain embeddings from the original
Boolean rings into the destination, and transport the pairing.

The exact source-image intersection and base commuting square transfer
along these isomorphisms, yielding **class-level strong amalgamation**.

## Final Fraïssé ingredients

Heredity is restriction to finite Boolean subrings on each sort and
restriction of the bilinear form. Joint embedding uses the two zero
rings as a common base. There are arbitrarily large members.
Countably many isomorphism types follow from finite atom presentations
and finitely many `F₂` matrices for each pair of atom-set cardinalities.
Fraïssé's theorem supplies the limit (an external standard implication).

For ω-categoricity, an `n`-tuple in a Boolean ring generates at most
`2^n−1` atoms (the all-zero membership pattern is absent). Each
two-sorted finite generated substructure, with its distinguished tuple
and pairing, therefore has one of finitely many isomorphism types.
Homogeneity gives finitely many automorphism orbits. The final
Ryll–Nardzewski theorem is an external standard citation unless an
end-to-end model-theoretic formalisation is explicitly added.

## Adversarial scope checks

- **No hidden unitality.** The atom-owner has codomain `Option`, and
  `none` target atoms must remain available as private points.
- **Trivial ring.** The zero ring has no atoms. Its atom representation
  is the singleton powerset of the empty set; nonempty-fibre conditions
  are vacuous.
- **Two sorts are independent.** The base atom maps and pivot choices
  on the left and right sorts are unrelated; the only compatibility
  condition on pairings is agreement on the common base product.
- **No shortcut from ring AP to pairing AP.** The actual destination
  pairing must extend the entire two input pairings, as established
  by #281.
- **No shortcut from finite orbit signatures to topology.** Stone
  measures, group amenability and automorphism-group topology remain
  separate obligations.

## Independent finite regression

The script `scripts/check_folkman_partial_owner_small.py`, added in
#283, enumerates all 74,963 singleton-image assignments for source
and target atom counts 0–4. It confirms that precisely 185 mappings
are injective Boolean-ring homomorphisms and each admits the required
partial owner. Ninety-two are genuinely non-unital; five tests have
zero source atoms. This does not replace the Lean proof.

**Status:** #282–#283 await their kernel checks. The final transport
between native abstract finite Boolean rings and their canonical
powersets, the packaged arbitrary-class AP and the limit consequences
have **not** yet been formalised as one exported theorem. No independent
agent instance is claimed by this audit.
