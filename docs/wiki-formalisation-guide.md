# Lean formalisation of BANANA

This repository accompanies *Parity obstructions to precompact Ramsey expansions* by Sofia Brenner, Jan Hubička, Colin Jahel and Jaroslav Nešetřil. This guide explains the mathematical representations, principal verified results, and the scope of the formalisation.

## How to read the formalisation

The library is imported by `BANANA.lean`; mathematical statements are in `BANANA/NonPrecompact`. The [proof coverage map](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/README.md#proof-coverage) gives declaration-level links. The [classical-dependency audit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/docs/classical-dependencies.md) explains the general results used in the article, their Lean counterparts, and the remaining cited inputs.

The manuscript's margin annotations have three meanings:

- **Lean ✓**: the linked statement has been checked in Lean.
- **Lean rel.**: the result is checked in a related representation or under an explicit interface; the mathematical correspondence must also be understood.
- **Lean part**: a checked component of a larger argument.

Kernel checking certifies the declared theorem; checking that the statement matches the manuscript is a separate mathematical task.

## Mathematical representations

**Boolean–BANANA.** The objects are finite nontrivial Boolean algebras with a parity marking. Constructions use finite atom representations and are transferred to unital Boolean-algebra embeddings preserving the marking. The concrete countable cylinder model realises the finite age; the dynamics use its pointwise automorphism group.

**Folkman–BANANA.** The objects consist of two finite Boolean rings with a biadditive pairing into the two-element field. Embeddings are injective non-unital ring homomorphisms preserving the pairing; zero rings are allowed. Amalgamation uses atom grids and private atoms outside the image of the base unit. The native Fraïssé-class theorem proves heredity, joint embedding, strong amalgamation, countability of isomorphism types and unbounded sizes. Lean packages these proofs in a record, not an additional assumption. A separate first-order development uses a Cartesian-product encoding of the two rings, checks the native embedding correspondence, constructs a countable categorical encoded limit, and decodes its native ring sorts and pairing with finite mixed-sort tuple-orbit bounds.

**BANANA.** Objects consist of two finite-dimensional vector spaces over the two-element field equipped with a possibly degenerate bilinear pairing. Coordinate presentations use rectangular matrices; embeddings preserve the pairing and copies are pairs of image subspaces. Native coherent EPPA applies to arbitrary finite carriers and gives a common perfect witness. The dynamics use the explicit countable pairing and its automorphisms. Model-theoretic statements use a tagged relational presentation, with decoding and sorted formula translation; the expansion argument also has a functional tagged presentation.

**Alternating spaces.** The age of the countable symplectic space consists of all finite-dimensional alternating spaces, including degenerate and zero-dimensional spaces. Embeddings are injective linear isometries; copies are image subspaces. The formalisation constructs the countable orthogonal sum and proves its finite-age and homogeneity properties.

## Principal results and entry points

These links are pinned to the verified source revision.

| Result | Lean source |
| --- | --- |
| Boolean–BANANA finite age, strong amalgamation and homogeneity | [BooleanBanana](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBanana.lean) |
| Folkman–BANANA Fraïssé-class theorem | [Native finite-class theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanNativeCompleteFiniteClass.lean#L85), [sortwise intersection](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanNativeSortwiseIntersection.lean) |
| Folkman–BANANA limit and categoricity | [Encoded Fraïssé class](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanFirstOrderFraisse.lean), [categorical encoded limit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanFirstOrderExistence.lean#L24), [native mixed-sort orbits](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanFirstOrderTaggedLimitOrbits.lean#L15) |
| BANANA age and homogeneity | [Finite age](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitFiniteAge.lean), [global homogeneity](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitGlobalHomogeneity.lean) |
| BANANA coherent EPPA | [Native coherent witness](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaNativeCoherentEppa.lean#L161) |
| BANANA amenability and ample generics | [Amenability](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitTopologicalAmenability.lean), [ample generics](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitGenericBackAndForth.lean#L285) |
| No precompact Ramsey expansions in the three classes | [Generated expansion types](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaGeneratedRamseyObstructions.lean), [native pointed-cover obstructions](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/NativePointedRamseyExpansion.lean#L119) |
| Exact BANANA and alternating-space Ramsey degrees | [BANANA copy degrees](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaOneSidedCopyDegree.lean#L157), [embedding-degree classifications](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/RamseyDegreeClassifications.lean#L15) |
| BANANA nonmetrisable universal minimal flow | [Native universal minimal flow](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitUniversalMinimalFlow.lean#L42) |
| Definable elementary embedding Ramsey property | [Sorted definable tuple Ramsey theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaSortedDefinableTupleRamsey.lean#L169) |
| Boolean–BANANA minimal charge flow with meagre orbits | [Concrete cylinder charge flow](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderPadicCharge.lean) |
| Continuum many conjugacy classes of closed maximal amenable subgroups | [Concrete positive-mass subgroups](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderMassSubgroups.lean#L31) |

## Scope of the expansion obstruction and classical inputs

The paper counts expansion types as isomorphism types of an expanded substructure generated by a reduct copy, together with that distinguished copy. Added functions or constants may enlarge the generated substructure. The [native degree-bound theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/NativePointedRamseyExpansion.lean#L72) uses a finite pointed cover, a composition-preserving reduct map and the expanded embedding Ramsey property. It yields the three native obstructions without assuming the reduct copy is closed under the added functions.

For an arbitrary many-sorted hereditary expansion, take the generated expanded substructure of each copy. Heredity supplies membership of the expanded age; a pointed isomorphism from a representative followed by inclusion supplies the required cover. This passage from arbitrary many-sorted syntax to the native interface is an English mathematical correspondence argument, not a separately kernel-checked syntax translation. The formal first-order generated-expansion theorem complements it. Relative annotations retain this distinction.

The library also verifies substantial classical results, including both directions of the countable categoricity/oligomorphicity correspondence and a native proof of nonmetrisability for BANANA. The general reverse implication in Ben Yaacov–Melleray–Tsankov's Theorem 1.1 remains cited. See the [dependency audit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/docs/classical-dependencies.md) for the exact scope of the other results.

## Reproducing the verification

The verified source revision is [`4fabdd7cf1bf`](https://github.com/janhubicka/lean-BANANA/commit/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf). Merged main `4205b301a5960dbabe5bdf7fa226db85307ea87a` has the identical source tree and passed its own ordinary CI run. The final release tag and author sign-off are pending.

Use the toolchain pinned in `lean-toolchain` (Lean 4.35.0-rc3) and the committed `lake-manifest.json`. Do not run `lake update` when reproducing this snapshot.

```sh
git clone https://github.com/janhubicka/lean-BANANA.git
cd lean-BANANA
git checkout 4fabdd7cf1bf1206912cd0d6c92e685b04e769cf
lake exe cache get
bash scripts/verify_release_candidate.sh
```

The [exact-head CI](https://github.com/janhubicka/lean-BANANA/actions/runs/45844957074) passed 261 steps, all 387 strict axiom-audit modules and 12 Python tests. All audited transitive axiom sets are contained in `propext`, `Classical.choice` and `Quot.sound`. The strict audit rejects unexpected axioms and mismatches between declaration queries and reports. The [archived verification logs](https://github.com/janhubicka/lean-BANANA/actions/runs/45844957074/artifacts/15132656205) record the checks. This concerns the audited declarations, not a claim that every sentence of the paper has been formalised.

The Lean software is licensed under [Apache-2.0](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/LICENSE). Cite the exact formalisation revision and the article for mathematical exposition. See [release instructions](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/docs/arxiv-release.md) and [citation metadata](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/CITATION.cff).
