# Track C integration audit — finite profiles to global Folkman orbits (7 November 2026)

**Internal note; not circulation prose. Draft, uncompiled Lean.** No manuscript
text or validation marker may be changed as part of this track.

## Confirmed upstream interface

Track B draft PR #309 now defines
`folkmanNativeFinCode_exists_atomEmbedding_with_maps` in
`FolkmanNativeFiniteClassMorphismWitness.lean`. Unlike the earlier
`Nonempty (FolkmanAtomEmbedding ...)` result in PR #305, it retains two
equalities for **every** finite source atom support:

```
folkmanNativeFinRingMap fL s = s.biUnion (folkmanFiber E.leftOwner)
folkmanNativeFinRingMap fR t = t.biUnion (folkmanFiber E.rightOwner)
```

The precise adapter into Track C's `FolkmanPresentedNativeEmbedding`
uses the existing equality
`folkmanNativeFinRingMap_apply f x`, applied to the source's
`folkmanNativeFiniteRingCodeEquiv` code. The latter code's inverse
cancels, yielding for all native elements `x`

```
folkmanNativeFiniteRingCodeEquiv BL (fL x) =
  (folkmanNativeFiniteRingCodeEquiv AL x).biUnion
    (folkmanFiber E.leftOwner)
```

and the analogous right-sort equation. This is exactly the `left_code`
and `right_code` pair of fields required by Track C.

The finite-object existence theorem
`folkmanNative_exists_finite_index_presentation` gives the
finite-index data accepted by
`FolkmanFinitePairingPresentation.ofCoordinates`:
carrier equivalences, zero, addition, multiplication, and pairing
reconstruction on **every** native pair. That is more than merely a
matrix invariant on the atom codes.

**Integration gate:** PR #309 is stacked on unverified PR #305; it cannot
be imported into PR #308 (based on main) yet without also importing
their unverified code. Do not copy and maintain duplicate finite-index
proofs. Wait for both to pass the pinned exact-head local Lean build,
their axiom audits, and independent statement review.

## Progress on Track C

The finite statement `FolkmanPresentedNativeEmbedding.tupleProfile_preserved`
now has the following two useful consequences in source:

* `folkmanTupleProfile_eq_of_commonPresentedExtension`: two compatible
  finite presentations of the same labelled tuple have identical
  complete profiles when they embed into a common finite stage;
* `folkmanTupleProfile_preserved_twoStep`: this equality transports
  through an intermediate stage, with no unsupported assertion that
  the arbitrary owner maps have already been composed in Lean.

These are **conditional finite** statements. They do not manufacture
common finite extensions or a countable limit.

## Essential remaining mathematical obligations

1. **Local finiteness of the specific limit:** work with a countable
   Fraïssé limit constructed as the union of finite Folkman stages,
   so every finite tuple lies in a finite stage. The fact that a class
   has finite members alone is not a substitute for this union/extension
   property.
2. **Native finite generated structures:** the substructure generated
   by a tuple is the non-unital `NonUnitalSubring.closure` on each
   Boolean-ring sort. It need not contain the ambient unit. Track B
   `FolkmanNativeFiniteHeredity.lean` constructs its *intrinsic* unit,
   allowing it to be treated as a finite Boolean ring while preserving
   the original named operations; this is still unverified.
3. **Uniform profile in the limit:** choose a finite stage containing
   the tuple, code it by faithful finite atom coordinates, and take
   `FolkmanAtomTupleProfile`. Use the compatible embedding witness
   and finite-stage independence to prove the result is well defined,
   including independence of atom enumeration and zero-pattern atoms.
   Do not assume it is well defined merely because its codomain is
   finite.
4. **Global automorphisms:** equal profiles imply, by Track C's
   `folkmanNativeGeneratedTwoSortIso_of_profile_eq`, a
   generator-preserving isomorphism of two finite generated
   substructures. This gives global orbit equivalence only after the
   countable limit has a formalised ultrahomogeneity/extension theorem.
5. **Finitely many orbits:** the existing
   `folkmanFiniteProfile_quotient_finite` and mixed-sort variant
   then apply. Their `hcomplete` premise must be discharged by step 4,
   not supplied as an arbitrary assumption in the final theorem.
   Ryll–Nardzewski may remain an explicitly cited external deduction.

## Adversarial checks and source quality

The accompanying seven finite regression scripts previously relied on
Python `assert`; under `python -O` the assertions vanish. All seven
now **fail closed** when `__debug__` is false. The exact-head
verification gate checks both the ordinary run and the expected
optimised-mode refusal. These commits touch only regression scripts
and the local gate.

A separate set/frozenset-based checker (rather than the repository
bit-mask implementation) was run in the model container on 7 November:

* 1,280 owner-map embedding configurations;
* 8,960 two-sort profile comparisons;
* 640 common-extension configurations;
* 4,480 common-extension profile comparisons;
* 566 common-stage configurations with an empty source sort.

It also tests pairings on all source ring elements, zero-pattern
exclusion, and preservation under union/intersection and symmetric
difference. SHA-256 of the executable independent-method
semantic checker:
`efa82917dbd1bbf901baff3c737947c0f33dd3e4770e8f4b4f03622cb4ea996c`.

**Limitations:** this is mathematical finite regression, not execution
of the Lean proofs and not an independently spawned referee. No Lean,
Lake or Elan is available in this runtime, and the container cannot
resolve github.com. Thus no local kernel build or axiom audit was run
on the new PR #308 head. The independent-adversarial-referee gate
remains outstanding.

## Local verification

At the exact clean Track C branch head:

```sh
bash scripts/verify_folkman_track_c_exact_head.sh "$(git rev-parse HEAD)"
```

This checks the module graph, builds all of BANANA with the pinned Lean
toolchain, audits all transitive axioms, and runs all seven finite
regressions in normal mode plus their optimised-mode refusal probes.
It does **not** dispatch GitHub Actions or any TeX workflow.

**Keep PR #308 as a draft and do not add manuscript validation markers
or merge until the kernel, axioms and independent referee checks pass.**
