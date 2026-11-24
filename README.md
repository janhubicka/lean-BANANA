# lean-BANANA

Lean 4 formalisation accompanying the BANANA manuscript.
[Manuscript source](https://github.com/janhubicka/BANANA)

## Proof coverage

| Development | Lean endpoints | Further steps in the manuscript |
| --- | --- | --- |
| pre-BANANA | The explicit cylinder algebra has the required finite age, is ultrahomogeneous and has finitely many automorphism orbits on tuples of each fixed length. The persistence proof uses finite atom coordinates. | The deduction of ω-categoricity uses Ryll–Nardzewski. The Stone action and the topological dynamics conclusions require separate arguments. |
| Folkman–BANANA | The finite class certificate covers heredity, countable representatives, unbounded sizes, joint embedding and strong amalgamation with native paired Boolean rings and non-unital embeddings. The persistent colouring and failure of each proposed finite copy bound now hold on the native rings. | Connecting the native obstruction to the abstract expansion interface, constructing the countable limit, and applying the finite tuple profiles to its global orbits remain open. The Stone-space argument is external. |
| BANANA | The explicit countable pairing has the stated finite age, homogeneity and finite tuple-orbit bounds. Lean checks the copy Ramsey degree classification, finite-system JEP and WAP, finite-stage GL approximation and the algebraic coherent-EPPA construction. | The passage from finite-system JEP and WAP to ample generics, the topological amenability and nonmetrisability deductions, the canonical-amalgamation deduction of DEERP and the full coherent-EPPA packaging are separate from these certificates. |
| Symplectic application | Lean checks the quadratic residue lemma, polar-form identities and the nondegenerate slice construction. | Assembly of the persistent colouring and the resulting copy-degree classification remains open. |

All paths in the following table are relative to the repository root. The
declarations are in the namespace `SuccessorTree.NonPrecompact`.

| Claim | Declaration and source |
| --- | --- |
| pre-BANANA finite age | [`prebananaCylinder_allFiniteModels_embed` and `prebananaCylinder_finiteSubmodel_factor`](BANANA/NonPrecompact/PrebananaFiveAryCylinderFiniteAge.lean) |
| pre-BANANA homogeneity | [`prebananaCylinder_exists_global_marked_boolean_automorphism`](BANANA/NonPrecompact/PrebananaFiveAryCylinderUltrahomogeneity.lean) |
| pre-BANANA finite tuple orbits | [`prebananaCylinderMarkedOrbit_finite`](BANANA/NonPrecompact/PrebananaFiveAryCylinderMarkedOrbitFiniteness.lean) |
| pre-BANANA atom-coordinate obstruction | [`prebananaTwoMarkedCopyRamseyDegree_infinite`](BANANA/NonPrecompact/PrebananaCopyDegree.lean) |
| Folkman–BANANA finite class | [`folkmanNativeCompleteFiniteClass_nonempty`](BANANA/NonPrecompact/FolkmanNativeCompleteFiniteClass.lean) |
| Folkman–BANANA native obstruction | [`folkmanNativeAxCopy_not_bounded`](BANANA/NonPrecompact/FolkmanNativeCopyTransport.lean) |
| Folkman–BANANA atom-coordinate obstruction | [`folkmanAxCopyRamseyDegree_infinite`](BANANA/NonPrecompact/FolkmanPersistence.lean) |
| BANANA finite age and homogeneity | [`banana_limit_finite_age_two_directions`](BANANA/NonPrecompact/BananaLimitFiniteAge.lean), [`exists_global_pair_automorphism_extends`](BANANA/NonPrecompact/BananaLimitGlobalHomogeneity.lean) |
| BANANA finite tuple orbits | [`bananaLimit_exists_finite_tuple_orbit_representatives`](BANANA/NonPrecompact/BananaLimitFiniteOrbits.lean) |
| BANANA copy Ramsey degrees | [`BananaMatrixStructure.copyRamseyDegree_classification`](BANANA/NonPrecompact/BananaOneSidedCopyDegree.lean) |
| BANANA algebraic EPPA construction | [`BananaMatrixStructure.exists_alignedCoherentAmbientAction`](BANANA/NonPrecompact/CoherentEppaPackage.lean) |
| BANANA finite-system JEP and WAP | [`bananaFiniteSystems_jep_and_wap`](BANANA/NonPrecompact/BananaFiniteSystemsJepWap.lean) |
| BANANA finite-stage GL approximation | [`bananaLimitFiniteGLUnion_pointwise_approximates`](BANANA/NonPrecompact/BananaLimitLocallyFiniteDense.lean) |
| BANANA canonical zero-base amalgamation | [`BananaMatrixStructure.exists_canonical_zero_amalgam`](BANANA/NonPrecompact/BananaDirectSumCanonical.lean) |
| Symplectic residue lemma | [`quadraticAffineWeight_residueFibres_odd`](BANANA/NonPrecompact/QuadraticResidueStandard.lean) |

The pre-BANANA embeddings are unital. The Folkman–BANANA embeddings
preserve the ring operations and zero separately in each sort, with
preservation of the pairing as an additional condition.

## Shared model-theory infrastructure

The [finite extension adapter](BANANA/NonPrecompact/FirstOrderFiniteExtension.lean)
uses mathlib's Fraïssé back-and-forth result to derive ultrahomogeneity from
finite extensions in a countable, locally finite first-order model.
Applying it to the existing native presentations requires a structure and
embedding bridge. For Folkman this bridge must preserve both sorts and their
pairing and allow non-unital embeddings. The countable model still needs to
be constructed with the finite extension property.

The BANANA and pre-BANANA orbit proofs share
[finite invariant counting](BANANA/NonPrecompact/FiniteInvariantRepresentatives.lean).
Their class-specific tuple profiles still prove that equal signatures lie
in the same automorphism orbit. The concrete cylinder construction and
the native strong amalgamation certificates also retain their separate
mathematical roles.

## Local verification

The commands below use the Lean version in `lean-toolchain` and the exact
dependency revisions in `lake-manifest.json`.

```sh
lake env lean --version
lake exe cache get
bash scripts/audit_all_axioms_local.sh
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The cache command is optional. The audit builds `BANANA`, checks the module
graph, runs every `*AxiomAudit.lean` file and requires one result for each
requested declaration. Its permitted transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The theorem statements record the
hypotheses of each certificate.

[arXiv release preparation](docs/arxiv-release.md)

[Classical dependency audit](docs/classical-dependencies.md)
