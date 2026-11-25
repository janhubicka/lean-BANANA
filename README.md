# lean-BANANA

Lean 4 formalisation accompanying the BANANA manuscript.
[Manuscript source](https://github.com/janhubicka/BANANA)

## Proof coverage

| Development | Lean endpoints | Further steps in the manuscript |
| --- | --- | --- |
| Boolean–BANANA | The explicit cylinder algebra has the required finite age, is ultrahomogeneous and has finitely many automorphism orbits on tuples of each fixed length. Lean checks the copy-degree obstruction and the failure of precompact Ramsey expansions in the shared expansion interface. The Stone action witnesses nonamenability of the actual pointwise automorphism group. Lean builds the compact metrisable charge space with its continuous action and proves orbit meagreness. The positive-mass development covers strong amalgamation on weighted atom grids, uniform-atom permutations and the finite-stage group embeddings. | The deduction of ω-categoricity uses Ryll–Nardzewski. Minimality still needs finite residue realisation in the concrete flow. Transport to the positive-mass class and the dense union in its limit require further arguments. |
| Folkman–BANANA | The finite class certificate covers heredity, countable representatives, unbounded sizes, joint embedding and strong amalgamation. Lean checks the first-order Fraïssé class. Its encoded countable limit was checked separately against the external Lean existence theorem. Lean recovers the native rings and pairing of that limit and proves finite mixed-sort tuple-orbit bounds. The native finite class fails EPPA. Lean checks the persistent colouring, infinite copy Ramsey degree and the failure of precompact Ramsey expansions in the shared expansion interface on native paired Boolean rings. | The passage from oligomorphicity to ω-categoricity uses Ryll–Nardzewski. The Stone-space nonamenability argument requires further work. |
| BANANA | The explicit countable pairing has the stated finite age, homogeneity and finite tuple-orbit bounds. Lean checks the copy Ramsey degree classification, coherent EPPA, finite-system JEP and WAP, and topological amenability from the dense increasing union of finite GL subgroups. | The passage from finite-system JEP and WAP to ample generics, the nonmetrisability deduction, and the canonical-amalgamation deduction of DEERP require further arguments. |
| Symplectic application | Lean checks the countable orthogonal sum, its finite age and homogeneity, amalgamation of finite alternating spaces, the persistent colouring of lines and the full classification of copy Ramsey degrees. | The classification uses actual image subspaces as copies, including degenerate and zero-dimensional spaces. |

All paths in the following table are relative to the repository root. The
declarations are in the namespace `SuccessorTree.NonPrecompact`.

| Claim | Declaration and source |
| --- | --- |
| Boolean–BANANA strong amalgamation | [`BooleanBanana.strongAmalgamation`](BANANA/NonPrecompact/BooleanBanana.lean) |
| Boolean–BANANA finite age | [`BooleanBanana.finiteModel_embeds_limit` and `BooleanBanana.finiteSubmodel_factors`](BANANA/NonPrecompact/BooleanBanana.lean) |
| Boolean–BANANA homogeneity | [`BooleanBanana.limit_automorphism_extends`](BANANA/NonPrecompact/BooleanBanana.lean) |
| Boolean–BANANA finite tuple orbits | [`BooleanBanana.limit_tupleOrbits_finite`](BANANA/NonPrecompact/BooleanBanana.lean) |
| Boolean–BANANA native copies and expansion obstruction | [`exists_booleanBananaPersistentColouring`, `booleanBananaTwoMarkedCopyRamseyDegree_infinite`, `booleanBanana_noPrecompactRamseyExpansion`](BANANA/NonPrecompact/BooleanBananaCopyTransport.lean) |
| Boolean–BANANA positive integer grid | [`BooleanBanana.exists_positive_integer_grid`](BANANA/NonPrecompact/BooleanBananaPositiveMassMargins.lean) |
| Boolean–BANANA rational mass grids and refinements | [`BooleanBanana.exists_common_positive_mass_denominator`, `BooleanBanana.exists_positive_mass_grid` and `BooleanBanana.exists_positive_mass_refinement`](BANANA/NonPrecompact/BooleanBananaPositiveMassArithmetic.lean) |
| Boolean–BANANA uniform atoms | [`BooleanBanana.uniform_atom_refinement_preserves` and `BooleanBanana.exists_uniform_atom_permutation`](BANANA/NonPrecompact/BooleanBananaPositiveMassUniformAtoms.lean) |
| Boolean–BANANA strong amalgamation on weighted atom grids | [`BooleanBanana.exists_positive_mass_strong_amalgam`](BANANA/NonPrecompact/BooleanBananaPositiveMassAmalgam.lean) |
| Boolean–BANANA cofinal denominators and permutation stages | [`BooleanBanana.exists_positive_mass_denominator_chain` and `BooleanBanana.uniformAtomPermLift_injective`](BANANA/NonPrecompact/BooleanBananaPositiveMassStages.lean) |
| Boolean–BANANA two-adic charge action | [`BooleanBanana.padicCharge_compactSpace`, `BooleanBanana.padicCharge_metrizableSpace` and `BooleanBanana.markedAutomorphisms_padicChargeAction_continuous`](BANANA/NonPrecompact/BooleanBananaPadicCharge.lean) |
| Boolean–BANANA two-adic charge existence | [`BooleanBanana.nonempty_padicCharge`](BANANA/NonPrecompact/BooleanBananaPadicChargeNonempty.lean) for any compatible marking on a nontrivial Boolean algebra |
| Boolean–BANANA arbitrary finite charge extension | [`BooleanBanana.exists_padicCharge_extension`](BANANA/NonPrecompact/BooleanBananaPadicChargeExtension.lean) |
| Boolean–BANANA meagre charge orbits | [`BooleanBanana.padicChargeOrbit_meagre`](BANANA/NonPrecompact/BooleanBananaPadicChargeOrbit.lean) |
| Boolean–BANANA charge orbit density given finite residue realisation | [`BooleanBanana.dense_padicChargeOrbit_of_finiteResidues`](BANANA/NonPrecompact/BooleanBananaPadicChargeMinimality.lean) |
| Boolean–BANANA nonamenability | [`BooleanBanana.limit_not_amenable`](BANANA/NonPrecompact/BooleanBananaStoneNonamenability.lean) |
| Folkman–BANANA finite class | [`folkmanNativeCompleteFiniteClass_nonempty`](BANANA/NonPrecompact/FolkmanNativeCompleteFiniteClass.lean) |
| Folkman–BANANA first-order embedding correspondence | [`folkmanNativePairingEmbeddingEquiv`](BANANA/NonPrecompact/FolkmanFirstOrder.lean) |
| Folkman–BANANA first-order substructure correspondence | [`folkmanProductSubstructureEquiv`](BANANA/NonPrecompact/FolkmanFirstOrderSubstructure.lean) |
| Folkman–BANANA first-order Fraïssé class | [`folkmanFirstOrderClass_isFraisse`](BANANA/NonPrecompact/FolkmanFirstOrderFraisse.lean) |
| First-order tuple orbits from a finite pointed cover | [`finite_firstOrderTupleOrbits_of_pointedCover`](BANANA/NonPrecompact/FirstOrderTupleOrbits.lean) uses mathlib's ultrahomogeneity interface |
| Native finite diagrams in the encoded Folkman–BANANA limit | [`folkmanFirstOrderLimit_nativeExtension` and `folkmanFirstOrderLimit_tuple_factors`](BANANA/NonPrecompact/FolkmanFirstOrderLimit.lean) |
| Folkman–BANANA original language recovered from finite tuple factorisations | [`FolkmanDecoding.encodingEquiv`](BANANA/NonPrecompact/FolkmanFirstOrderDecoding.lean) |
| Folkman–BANANA mixed-sorted orbit transfer | [`FolkmanDecoding.exists_finite_tagged_tuple_orbit_representatives_of_invariant`](BANANA/NonPrecompact/FolkmanFirstOrderTaggedOrbits.lean) transfers finite orbit data from encoded tuples to tuples with specified sorts |
| Folkman–BANANA native limit and finite mixed tuple orbits | [`FolkmanDecoding.folkmanFirstOrderLimit_exists_finite_tagged_tuple_orbit_representatives`](BANANA/NonPrecompact/FolkmanFirstOrderTaggedLimitOrbits.lean) |
| Folkman–BANANA two-atom EPPA obstruction | [`folkmanTwoAtom_partialIso_obstructed`](BANANA/NonPrecompact/FolkmanFiniteBooleanEPPA.lean) |
| Folkman–BANANA fails EPPA in the native class | [`folkmanNativeEPPA_fails`](BANANA/NonPrecompact/FolkmanNativeEPPAObstruction.lean) |
| Folkman–BANANA native copies and expansion obstruction | [`exists_folkmanNativeCopyRangeColouring`, `folkmanNativeCopyRamseyDegree_infinite`, `folkmanNative_noPrecompactRamseyExpansion`](BANANA/NonPrecompact/FolkmanRamseyExpansionObstruction.lean) |
| Folkman–BANANA atom-coordinate obstruction | [`folkmanAxCopyRamseyDegree_infinite`](BANANA/NonPrecompact/FolkmanPersistence.lean) |
| BANANA finite age and homogeneity | [`banana_limit_finite_age_two_directions`](BANANA/NonPrecompact/BananaLimitFiniteAge.lean), [`exists_global_pair_automorphism_extends`](BANANA/NonPrecompact/BananaLimitGlobalHomogeneity.lean) |
| BANANA finite tuple orbits | [`bananaLimit_exists_finite_tuple_orbit_representatives`](BANANA/NonPrecompact/BananaLimitFiniteOrbits.lean) |
| BANANA copy Ramsey degrees | [`BananaMatrixStructure.copyRamseyDegree_classification`](BANANA/NonPrecompact/BananaOneSidedCopyDegree.lean) |
| BANANA coherent EPPA | [`BananaMatrixStructure.exists_coherentEppaWitness`](BANANA/NonPrecompact/CoherentEppaWitness.lean), a single perfect witness with both sides of dimension `l+r` and a coherent assignment for all partial isomorphisms |
| BANANA finite-system JEP and WAP | [`bananaFiniteSystems_jep_and_wap`](BANANA/NonPrecompact/BananaFiniteSystemsJepWap.lean) |
| BANANA dense finite GL approximation and amenability | [`exists_bananaLimitFiniteGLSequence` and `bananaLimitAutomorphismGroup_amenable`](BANANA/NonPrecompact/BananaLimitTopologicalAmenability.lean) |
| Amenability of a dense directed union of finite subgroups | [`exists_invariant_probability_of_dense_finite_subgroups`](BANANA/NonPrecompact/FiniteSubgroupAmenability.lean) |
| Fixed-point method for finite colour palettes | [`exists_fixed_colouring_in_orbit_closure` and `exists_finite_support_of_orbit_fixed_colourings`](BANANA/NonPrecompact/FixedPointColouring.lean) |
| BANANA canonical zero-base amalgamation | [`BananaMatrixStructure.exists_canonical_zero_amalgam`](BANANA/NonPrecompact/BananaDirectSumCanonical.lean) |
| Symplectic residue lemma | [`quadraticAffineWeight_residueFibres_odd`](BANANA/NonPrecompact/QuadraticResidueStandard.lean) |
| Symplectic finite persistent line colouring | [`exists_symplecticPointColouring`](BANANA/NonPrecompact/SymplecticPointColouring.lean) |
| Symplectic homogeneity under the ambient hypotheses | [`exists_wittCountableIsometry`](BANANA/NonPrecompact/WittCountable.lean) |
| Concrete symplectic age and homogeneity | [`countableSymplectic_finite_age` and `exists_countableSymplectic_automorphism`](BANANA/NonPrecompact/SymplecticCountableModel.lean) |
| Symplectic amalgamation and copy Ramsey degrees | [`FiniteAlternatingSpace.exists_amalgam`](BANANA/NonPrecompact/SymplecticCopySystem.lean) and [`FiniteAlternatingSpace.copyRamseyDegree_classification`](BANANA/NonPrecompact/SymplecticCopyDegree.lean) |

## Manuscript notation

| Manuscript notation | Lean representation |
| --- | --- |
| `𝒦_bool`, `M_bool` | [`BooleanBanana.FiniteModel`, `BooleanBanana.limit`](BANANA/NonPrecompact/BooleanBanana.lean) |
| `A_bool`-copies and `B_bool(q)` | [`BooleanBananaCopy`](BANANA/NonPrecompact/BooleanBananaCopySystem.lean) for the two-marked-atom source and [`booleanBananaAllMarkedPower k`](BANANA/NonPrecompact/BooleanBananaCopyTransport.lean) for `q = 2^(k+1)` |
| `𝒦_folk`, `A_folk`-copies and `B_folk(q)` | [Native finite class](BANANA/NonPrecompact/FolkmanNativeCompleteFiniteClass.lean), [`FolkmanNativeAxCopy`](BANANA/NonPrecompact/FolkmanNativeCopyTransport.lean) and [`FolkmanAtomStructure.diagonal q`](BANANA/NonPrecompact/FolkmanPersistence.lean) |
| `A_b` and `B_D` for BANANA | [`linePairSource b`](BANANA/NonPrecompact/LinePairSourceEmbedding.lean) and [`perfectBanana D`](BANANA/NonPrecompact/BananaStructure.lean) |
| Pairing `β_A` and embedding components `f_L`, `f_R` for BANANA | [`A.eval`, `f.left`, `f.right`](BANANA/NonPrecompact/BananaStructure.lean) |

Boolean join and meet are `⊔` and `⊓` in Lean. In atom-set coordinates
they become union and intersection. The Boolean–BANANA embeddings are
unital. The Folkman–BANANA embeddings
preserve the ring operations and zero separately in each sort, with
preservation of the pairing as an additional condition. The Boolean–BANANA
entry point reuses the existing `Prebanana*` modules cited by pinned manuscript links.

## Shared model-theory infrastructure

The [finite extension adapter](BANANA/NonPrecompact/FirstOrderFiniteExtension.lean)
uses mathlib's Fraïssé back-and-forth result to derive ultrahomogeneity from
finite extensions in a countable, locally finite first-order model.
For Folkman–BANANA, the first-order product presentation uses coordinate
projections to distinguish the sorts and recovers the original non-unital
ring embeddings with their pairing. Its substructures are products of
non-unital subrings with the restricted pairing. The encoded countable
limit was checked by instantiating Freer's Fraïssé existence theorem.
See the [classical dependency audit](docs/classical-dependencies.md) for the
external revision and reproduction details.

The BANANA and Boolean–BANANA orbit proofs share
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
