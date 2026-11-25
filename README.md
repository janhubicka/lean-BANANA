# lean-BANANA

Lean 4 formalisation accompanying the BANANA manuscript.
[Manuscript source](https://github.com/janhubicka/BANANA)

## Proof coverage

| Development | Lean endpoints | Further steps in the manuscript |
| --- | --- | --- |
| Boolean–BANANA | Lean checks the concrete cylinder model and its finite age, homogeneity, tuple-orbit bounds and copy-degree obstruction. It proves nonamenability and builds a compact metrisable minimal two-adic charge flow with no comeagre orbit. For every nonempty set of odd primes, Lean constructs a positive-mass expansion of the fixed marked limit, proves its unique invariant regular Stone probability and verifies the continuum count of conjugacy classes of closed maximal amenable subgroups. | Lean also proves that the complete theory of the concrete marked Boolean cylinder is countably categorical. |
| Folkman–BANANA | The finite class certificate covers heredity, countable representatives, unbounded sizes, joint embedding and strong amalgamation. Lean checks the first-order Fraïssé class. Lean constructs its countable encoded Fraïssé limit using mathlib’s direct limits and back-and-forth. Lean recovers the native rings and pairing of that limit and proves finite mixed-sort tuple-orbit bounds. The native finite class fails EPPA. Lean checks the persistent colouring, infinite copy Ramsey degree and the failure of precompact Ramsey expansions in the shared expansion interface on native paired Boolean rings. Lean proves nonamenability of the native paired automorphism group in its pointwise topology, using the open interval stabiliser and Stone-space contradiction. | The constructed encoded limit is countably infinite and its complete theory is countably categorical. |
| BANANA | Lean verifies the finite age, homogeneity and tuple-orbit bounds of the explicit countable pairing, along with copy Ramsey degrees, coherent EPPA, and finite-system JEP and WAP. The tagged relational presentation is countably categorical, and every model of its theory recovers its two vector spaces and bilinear pairing. The native pointwise automorphism group is Polish and amenable and has no co-precompact extremely amenable subgroup. | Lean proves ample generics, constructs a nonmetrisable universal minimal flow, and verifies DEERP and first-order extreme amenability for the complete tagged theory. Lean also checks the canonical-amalgamation implication and the equivalence between DEERP and an invariant enumeration type under finite type isolation. |
| Symplectic application | Lean checks the countable orthogonal sum, its finite age and homogeneity, amalgamation of finite alternating spaces, the persistent colouring of lines and the full classification of copy Ramsey degrees. | The classification uses actual image subspaces as copies, including degenerate and zero-dimensional spaces. |

All paths in the following table are relative to the repository root. The
declarations are in the namespace `SuccessorTree.NonPrecompact`.

| Claim | Declaration and source |
| --- | --- |
| Boolean–BANANA strong amalgamation | [`BooleanBanana.strongAmalgamation`](BANANA/NonPrecompact/BooleanBanana.lean) |
| Boolean–BANANA finite age | [`BooleanBanana.finiteModel_embeds_limit` and `BooleanBanana.finiteSubmodel_factors`](BANANA/NonPrecompact/BooleanBanana.lean) |
| Boolean–BANANA homogeneity | [`BooleanBanana.limit_automorphism_extends`](BANANA/NonPrecompact/BooleanBanana.lean) |
| Boolean–BANANA countable categoricity | [`cylinderMarkedBoolean_categorical_completeTheory`](BANANA/NonPrecompact/BooleanBananaFirstOrderCategoricity.lean) |
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
| Boolean–BANANA charge orbit density given finite residue partitions | [`BooleanBanana.dense_padicChargeOrbit_of_partitions`](BANANA/NonPrecompact/BooleanBananaPadicChargeResidueApproximation.lean) |
| Boolean–BANANA charge orbit density given finite residue realisation | [`BooleanBanana.dense_padicChargeOrbit_of_finiteResidues`](BANANA/NonPrecompact/BooleanBananaPadicChargeMinimality.lean) |
| Boolean–BANANA positive-mass reasonability and heredity | [`BooleanBanana.positiveMass_reasonable` and `BooleanBanana.positiveMass_restrict`](BANANA/NonPrecompact/BooleanBananaPositiveMassReasonable.lean) |
| Boolean–BANANA positive-mass EPPA | [`BooleanBanana.positiveMass_eppa`](BANANA/NonPrecompact/BooleanBananaPositiveMassEPPA.lean) |
| Boolean–BANANA finite positive-mass class | [`BooleanBanana.positiveMass_strongAmalgamation`](BANANA/NonPrecompact/BooleanBananaPositiveMassStrongAP.lean), [joint embedding and expansion existence](BANANA/NonPrecompact/BooleanBananaPositiveMassJEP.lean), [countable representatives and unbounded sizes](BANANA/NonPrecompact/BooleanBananaPositiveMassCodes.lean) |
| Boolean–BANANA uniform-stage extension | [`BooleanBanana.positiveMass_uniformTower_extension`](BANANA/NonPrecompact/BooleanBananaPositiveMassLimitStages.lean) |
| Boolean–BANANA uniform tower group actions and dense union | [`BooleanBanana.UniformMassTower.finiteStage_dense`, `BooleanBanana.UniformMassTower.uniformMassCover` and `BooleanBanana.UniformMassTower.massSubgroup_amenable`](BANANA/NonPrecompact/BooleanBananaPositiveMassLimitGroups.lean) |
| Boolean–BANANA charge-flow theorem from marked homogeneity and all-marked finite ambients | [`BooleanBanana.padicChargeOrbit_dense_meagre_of_homogeneous_allMarked`](BANANA/NonPrecompact/BooleanBananaPadicChargeResiduePartition.lean) |
| Boolean–BANANA cylinder charge flow and failure of the generic point property | [`BooleanBanana.cylinderPadicChargeOrbit_dense_meagre` and `BooleanBanana.cylinderMarkedGroup_failsGenericPointProperty`](BANANA/NonPrecompact/BooleanBananaCylinderPadicCharge.lean) |
| Boolean–BANANA realised mass values and parity | [`BooleanBanana.exists_positiveMass_element_of_age`, `BooleanBanana.positiveMass_prime_mem_iff_of_age`, `BooleanBanana.exists_even_marked_mass_sequence_of_age`](BANANA/NonPrecompact/BooleanBananaMassRangeRealisation.lean) |
| Boolean–BANANA positive-mass subgroup dynamics | [`BooleanBanana.massSubgroup_eq_of_amenable_supergroup`, `BooleanBanana.invariantStoneProbability_unique`, `BooleanBanana.massSubgroup_no_stone_fixedPoint`, `BooleanBanana.massRange_eq_of_conjugate` and `BooleanBanana.massSubgroup_not_coprecompact`](BANANA/NonPrecompact/BooleanBananaMassStoneDynamics.lean) |
| Extension of clopen probability charges | [`existsUnique_regularProbability_of_clopenCharge`](BANANA/NonPrecompact/ClopenProbabilityExtension.lean) |
| Boolean–BANANA prime detection from mass values | [`BooleanBanana.prime_mem_iff_normalizedMass_mem_range`](BANANA/NonPrecompact/BooleanBananaMassPrimeRange.lean) |
| Boolean–BANANA concrete positive-mass expansions | [Weighted extension and reduct identification](BANANA/NonPrecompact/BooleanBananaPositiveMassOnMarkedLimit.lean) and [the mass-preserving subgroups of the fixed limit](BANANA/NonPrecompact/BooleanBananaCylinderMassSubgroups.lean) |
| Boolean–BANANA continuum many conjugacy classes of closed maximal amenable subgroups | [`BooleanBanana.mk_cylinderClosedMaximalAmenableConjugacyClass`](BANANA/NonPrecompact/BooleanBananaCylinderMassSubgroups.lean) |
| Boolean–BANANA nonamenability | [`BooleanBanana.limit_not_amenable`](BANANA/NonPrecompact/BooleanBananaStoneNonamenability.lean) |
| Folkman–BANANA finite class | [`folkmanNativeCompleteFiniteClass_nonempty`](BANANA/NonPrecompact/FolkmanNativeCompleteFiniteClass.lean) |
| Folkman–BANANA first-order embedding correspondence | [`folkmanNativePairingEmbeddingEquiv`](BANANA/NonPrecompact/FolkmanFirstOrder.lean) |
| Folkman–BANANA first-order substructure correspondence | [`folkmanProductSubstructureEquiv`](BANANA/NonPrecompact/FolkmanFirstOrderSubstructure.lean) |
| Folkman–BANANA first-order Fraïssé class | [`folkmanFirstOrderClass_isFraisse`](BANANA/NonPrecompact/FolkmanFirstOrderFraisse.lean) |
| Existence and countable categoricity of the encoded Folkman–BANANA limit | [`exists_folkmanFirstOrderLimit_categorical`](BANANA/NonPrecompact/FolkmanFirstOrderExistence.lean) |
| First-order tuple orbits from a finite pointed cover | [`finite_firstOrderTupleOrbits_of_pointedCover`](BANANA/NonPrecompact/FirstOrderTupleOrbits.lean) uses mathlib's ultrahomogeneity interface |
| Native finite diagrams in the encoded Folkman–BANANA limit | [`folkmanFirstOrderLimit_nativeExtension` and `folkmanFirstOrderLimit_tuple_factors`](BANANA/NonPrecompact/FolkmanFirstOrderLimit.lean) |
| Folkman–BANANA original language recovered from finite tuple factorisations | [`FolkmanDecoding.encodingEquiv`](BANANA/NonPrecompact/FolkmanFirstOrderDecoding.lean) |
| Folkman–BANANA mixed-sorted orbit transfer | [`FolkmanDecoding.exists_finite_tagged_tuple_orbit_representatives_of_invariant`](BANANA/NonPrecompact/FolkmanFirstOrderTaggedOrbits.lean) transfers finite orbit data from encoded tuples to tuples with specified sorts |
| Folkman–BANANA native limit and finite mixed tuple orbits | [`FolkmanDecoding.folkmanFirstOrderLimit_exists_finite_tagged_tuple_orbit_representatives`](BANANA/NonPrecompact/FolkmanFirstOrderTaggedLimitOrbits.lean) |
| Folkman–BANANA two-atom EPPA obstruction | [`folkmanTwoAtom_partialIso_obstructed`](BANANA/NonPrecompact/FolkmanFiniteBooleanEPPA.lean) |
| Folkman–BANANA fails EPPA in the native class | [`folkmanNativeEPPA_fails`](BANANA/NonPrecompact/FolkmanNativeEPPAObstruction.lean) |
| Folkman–BANANA interval transitivity and partitions | [`folkmanLeftInterval_stabilizer_transitive` and `folkmanLeftElement_exists_finiteIntervalEmbedding`](BANANA/NonPrecompact/FolkmanFirstOrderInterval.lean) |
| Folkman–BANANA native nonamenability | [`FolkmanDecoding.folkmanNativeLimit_not_amenable`](BANANA/NonPrecompact/FolkmanFirstOrderLimitNonamenability.lean) |
| Amenability of open subgroups | [`BooleanBanana.isTopologicallyAmenable_openSubgroup`](BANANA/NonPrecompact/OpenSubgroupAmenability.lean) |
| Copy Ramsey-degree bound from co-precompact extreme amenability | [`firstOrderFiniteCopyDegree_of_coprecompactExtremelyAmenable`](BANANA/NonPrecompact/FirstOrderExtremelyAmenableDegree.lean) |
| Tuple-orbit co-precompactness and closure criteria | [`FirstOrderAut.coprecompact_iff_finset_tupleOrbitRepresentatives` and `FirstOrderAut.mem_topologicalClosure_iff_preserves_tupleOrbits`](BANANA/NonPrecompact/FirstOrderOrbitCoPrecompact.lean) |
| Countable categoricity from oligomorphicity | [`categorical_completeTheory_of_finite_tupleOrbitRepresentatives`](BANANA/NonPrecompact/FirstOrderOligomorphicCategoricity.lean) |
| Oligomorphicity from countable categoricity | [`finite_tupleOrbitRepresentatives_of_categorical_completeTheory`](BANANA/NonPrecompact/FirstOrderOmittingTypes.lean) |
| Canonical orbit expansions | [`FirstOrderAut.range_restrictOrbitExpansionAut` and `FirstOrderAut.categorical_orbitExpansion_of_coprecompact`](BANANA/NonPrecompact/FirstOrderOrbitExpansion.lean) |
| Folkman–BANANA native copies and expansion obstruction | [`exists_folkmanNativeCopyRangeColouring`, `folkmanNativeCopyRamseyDegree_infinite`, `folkmanNative_noPrecompactRamseyExpansion`](BANANA/NonPrecompact/FolkmanRamseyExpansionObstruction.lean) |
| Folkman–BANANA atom-coordinate obstruction | [`folkmanAxCopyRamseyDegree_infinite`](BANANA/NonPrecompact/FolkmanPersistence.lean) |
| BANANA finite age and homogeneity | [`banana_limit_finite_age_two_directions`](BANANA/NonPrecompact/BananaLimitFiniteAge.lean), [`exists_global_pair_automorphism_extends`](BANANA/NonPrecompact/BananaLimitGlobalHomogeneity.lean) |
| BANANA finite tuple orbits | [`bananaLimit_exists_finite_tuple_orbit_representatives`](BANANA/NonPrecompact/BananaLimitFiniteOrbits.lean) |
| Countable categoricity of the tagged BANANA limit | [`bananaLimit_firstOrder_aleph0_categorical`](BANANA/NonPrecompact/BananaLimitFirstOrder.lean) |
| BANANA copy Ramsey degrees | [`BananaMatrixStructure.copyRamseyDegree_classification`](BANANA/NonPrecompact/BananaOneSidedCopyDegree.lean) |
| BANANA precompact Ramsey expansion obstruction | [`banana_noPrecompactRamseyExpansion`](BANANA/NonPrecompact/BananaNativeCopySystem.lean) uses the genuine BANANA copy ranges and the shared hereditary expansion interface |
| Copy degrees bounded by expansion isomorphism types | [`copyRamseyDegreeLE_card_expansionIsomorphismTypes`](BANANA/NonPrecompact/ExpansionDegreeByIsomorphismTypes.lean) quotients labelled expansions by reduct automorphisms |
| BANANA coherent EPPA | [`BananaMatrixStructure.exists_coherentEppaWitness`](BANANA/NonPrecompact/CoherentEppaWitness.lean), a single perfect witness with both sides of dimension `l+r` and a coherent assignment for all partial isomorphisms |
| BANANA finite-system JEP and WAP | [`bananaFiniteSystems_jep_and_wap`](BANANA/NonPrecompact/BananaFiniteSystemsJepWap.lean) |
| BANANA dense diagonal conjugacy orbits | [`bananaLimit_exists_dense_diagonalConjugacyOrbit`](BANANA/NonPrecompact/BananaLimitDenseConjugacy.lean) gives a dense orbit in each finite power |
| BANANA ample generics | [`bananaLimit_exists_comeagre_diagonalConjugacyOrbit`](BANANA/NonPrecompact/BananaLimitGenericBackAndForth.lean) gives one comeagre orbit in each finite power |
| BANANA dense finite GL approximation and amenability | [`exists_bananaLimitFiniteGLSequence` and `bananaLimitAutomorphismGroup_amenable`](BANANA/NonPrecompact/BananaLimitTopologicalAmenability.lean) |
| BANANA pointwise topology | [Polishness](BANANA/NonPrecompact/BananaLimitPolish.lean) and [native tuple-orbit criteria for co-precompactness and closure](BANANA/NonPrecompact/BananaLimitOrbitCoPrecompact.lean) |
| BANANA native and tagged automorphism groups | [Continuous group isomorphism and countable categoricity of canonical orbit expansions](BANANA/NonPrecompact/BananaLimitFirstOrderAutomorphism.lean) |
| BANANA has no co-precompact extremely amenable subgroup | [`bananaLimit_no_coprecompact_extremelyAmenable`](BANANA/NonPrecompact/BananaLimitExtremelyAmenableDegree.lean) |
| Existence and nonmetrisability of the BANANA universal minimal flow | [`bananaLimit_exists_nonmetrizable_universalMinimalFlow`](BANANA/NonPrecompact/BananaLimitUniversalMinimalFlow.lean) |
| No countably categorical tagged BANANA expansion has an extremely amenable group | [`bananaLimit_expansion_not_extremelyAmenable_of_countablyCategorical`](BANANA/NonPrecompact/BananaLimitExpansionGroup.lean) |
| Amenability of a dense directed union of finite subgroups | [`exists_invariant_probability_of_dense_finite_subgroups`](BANANA/NonPrecompact/FiniteSubgroupAmenability.lean) |
| Fixed-point method for finite colour palettes | [`exists_fixed_colouring_in_orbit_closure` and `exists_finite_support_of_orbit_fixed_colourings`](BANANA/NonPrecompact/FixedPointColouring.lean) |
| BANANA canonical zero-base amalgamation | [`BananaMatrixStructure.exists_canonical_zero_amalgam`](BANANA/NonPrecompact/BananaDirectSumCanonical.lean) |
| Finite parameter colourings in the native BANANA limit | [`exists_bananaLimit_monochromatic_target_of_finite_parameters`](BANANA/NonPrecompact/BananaLimitParameterColouring.lean) |
| DEERP and first-order extreme amenability of the complete tagged BANANA theory | [`bananaTagged_completeTheory_hasDefinableTupleRamsey`](BANANA/NonPrecompact/BananaLimitDefinableColouring.lean) and [`bananaTagged_completeTheory_exists_invariantEnumerationType`](BANANA/NonPrecompact/BananaLimitInvariantTypes.lean) |
| Two-sorted pairing decoded from any model of the complete tagged BANANA theory | [`bananaTaggedModelPairingEquiv`](BANANA/NonPrecompact/BananaTaggedModelDecoding.lean) |
| Truth-preserving translations and complete finite tuple types for BANANA’s two-sorted language | [`BananaSorted.Formula.realize_translate_decoded`](BANANA/NonPrecompact/BananaSortedSyntax.lean) and [`sameFormulaType_iff_sorted`](BANANA/NonPrecompact/BananaTaggedSyntaxReverse.lean) |
| Canonical age amalgamation and invariant extensions | [`exists_invariantExtension_of_canonicalAgeAmalgamation`](BANANA/NonPrecompact/FirstOrderCanonicalAmalgamation.lean) |
| Definable tuple Ramsey and invariant enumeration types | [With isolated finite types](BANANA/NonPrecompact/FirstOrderInvariantEnumerationRamsey.lean) and [with saturation and strong finite homogeneity](BANANA/NonPrecompact/FirstOrderInvariantEnumerationRamseySaturated.lean) |
| Coalescence and uniqueness of universal minimal flows | [`universalMinimalFlow_coalescent` and `universalMinimalFlow_unique`](BANANA/NonPrecompact/UniversalMinimalFlowUniqueness.lean) |
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
non-unital subrings with the restricted pairing. The construction of the
encoded countable limit schedules finite embedding requests and uses
mathlib's direct-limit and back-and-forth API.

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
