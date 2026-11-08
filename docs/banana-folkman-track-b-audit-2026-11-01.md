# BANANA Track B — Folkman finite native class (internal audit, 1 November 2026)

**Status: DRAFT / NOT KERNEL VERIFIED.** The circulation prose is frozen. This
branch changes Lean modules, axiom-audit modules, a regression and this internal
note only; it does not touch the TeX manuscript or the integration-owned
`BANANA.lean`. It branches from the exact draft head of PR #305
(`7928adf9c6749fe885c5a4f8be6b08a17fd89cfe`), so it depends on PR #305
being compiled and reviewed before integration.

## Statement-fidelity referee

The statement in `folkman-class.tex` (Proposition
`prop:folkman-fraisse`) is about **the original two-sorted language**:
non-unital Boolean rings `(+, *, 0)` and an F2-valued pairing additive in
each coordinate. Embeddings are injective *non-unital* ring homomorphisms in
both sorts and preserve that pairing. The complete Fraisse-class conclusion
requires HP, JEP, AP, finite isomorphism types and arbitrarily large objects.

Verified merged components prior to this branch include the original-language
hereditary pairing pullback (FolkmanNativeFinitePairingClass), the six-ring
strong-amalgamation certificate with exact image intersection
(FolkmanNativeStrongAmalgamPackage, PR #297), JEP over two zero rings
(FolkmanNativeJEP, PR #299), and countability/unboundedness of atom codes
(FolkmanFiniteClassData, PR #298). The finite native-to-atom coordinate
equivalence and pairing reconstruction are in **unverified** PR #305.

New interface `FolkmanNativeFiniteClassInterface.lean` uses packaged
`FolkmanNativeFinitePairing` data rather than splitting pairing hypotheses
through every call. It exposes exact native finite codes, their countability
and unboundedness, original-language JEP and strong AP. The associated
axiom-audit module records precise theorem names for the local gate.

The previous theorem `folkmanNativeFinCode_exists_atomEmbedding` in PR #305
only concludes `Nonempty (FolkmanAtomEmbedding ...)`. That *statement* does
not identify which atom-owner map represents the supplied native embedding,
even though its proof internally obtains the correct owners. New
`folkmanNativeFinCode_exists_atomEmbedding_with_maps` records the equalities
on **every** finite support for both sorts; the theorem is unverified until
elaboration. The old API is unchanged, so no other track is blocked.

## Independent finite counterexample audit

`scripts/check_folkman_track_b_strong_ap_small.py` exhaustively enumerates
both left and right atom diagrams with 0, 1 or 2 base/side atoms and all
surjective-to-source `Option` owners. For each it constructs exactly the
fibre grid plus distinct private outside atoms. It checks zero, XOR
(addition), intersection (multiplication), injectivity, base commutativity
and **exact strong image intersections** on all ring elements.

For each pair of arbitrary B/C atom matrices it tests base compatibility,
constructs the complete F2 linear system for the proposed amalgam pairing,
and checks solvability. It also verifies the resulting pairing on **all**
original B/C ring elements (not only on their atoms).

An independent local run of the corresponding script produced:

- 841 two-sort amalgamation diagrams;
- 34,403 base-compatible input pairing configurations, all extendible;
- 34,514 base-incompatible configurations, all correctly inconsistent.

These numbers count finite regression cases, **not Lean-proved cases**.
The zero ring, unowned target atoms, mixed-sort degeneracies, arbitrary
pairings and both permutations of a two-atom base occur in the enumeration.

## Outstanding obligations before Track B is complete

1. **Kernel gate:** on the exact composite branch head run
   `python3 scripts/check_lean_module_graph.py`,
   `lake build BANANA.NonPrecompact.FolkmanNativeFiniteClassInterface`,
   `lake build BANANA.NonPrecompact.FolkmanNativeFiniteClassMorphismWitness`,
   `lake env lean` on both new axiom-audit modules,
   `lake build BANANA`, and
   `bash scripts/audit_all_axioms_local.sh`. Only expected transitive axioms:
   `propext`, `Classical.choice`, `Quot.sound`. Runners are out of budget;
   do **not** run GitHub Actions as a substitute.
2. **Unverified upstream:** compile/review all PR #305 modules first;
   specifically the `AsBoolAlg` `Fintype` instance, `Finset.sum_map`
   rewrites, `Finset.mem_map_equiv`, and F2 count casting. The new
   declarations inherit that dependency.
3. **Full class packaging:** move from this collection of parameterised
   properties to a single explicit original-language finite-class/Fraisse
   interface, including representatives of every native isomorphism type.
   Countability and unboundedness of *codes* must be transported into the
   native class; code unboundedness alone is not yet an explicit native
   object constructor. Preserve the zero ring and unowned atoms.
4. **Morphisms:** verify owner-map equations, their compatibility with
   composition, and exact image intersection under the native/code bridge.
   Avoid conflating ring embeddings with arbitrary linear maps.
5. **Referee independence:** the mathematical review and finite regression
   are distinct checks, but no independent model referee or Lean kernel
   verifier was spawned in this environment. A separate theorem statement
   audit is still required.

The existing manuscript PR #241 already carries the relevant validation
TODOs. In particular, do not reintroduce any removed/commented-out notes.
The old TODO claiming that combined two-sorted pairing-preserving
amalgamation remains unformalised is stale relative to merged PR #297, but
manuscript annotation belongs to the designated integration track after
the exact-head proof gate. No prose changes are authorised here.
