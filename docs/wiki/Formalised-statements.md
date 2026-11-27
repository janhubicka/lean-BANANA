# Formalised statements: a manuscript-to-Lean crosswalk

**Evidence baseline:** [`4fabdd7cf1bf1206912cd0d6c92e685b04e769cf`](https://github.com/janhubicka/lean-BANANA/commit/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf), with the complete strict [kernel and axiom audit](https://github.com/janhubicka/lean-BANANA/actions/runs/45844957074). The crosswalk covers the circulation part of the paper, not its internal supplement. It uses the mathematical names of results rather than historical implementation labels.

## Three classes and their Fraïssé limits

| Manuscript result | Main Lean source | Scope |
| --- | --- | --- |
| Boolean–BANANA strong amalgamation, age and homogeneity | [BooleanBanana interface](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBanana.lean#L21) | Native unital Boolean embeddings preserving the parity marking; concrete countable cylinder limit |
| Boolean–BANANA countable categoricity | [Marked Boolean first-order categoricity](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaFirstOrderCategoricity.lean#L96) | Complete theory of the concrete marked limit |
| Folkman–BANANA strong amalgamation Fraïssé class | [Native finite-class theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanNativeCompleteFiniteClass.lean#L85); [Separate sortwise intersections](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanNativeSortwiseIntersection.lean) | All five finite-class ingredients, actual Boolean-ring amalgam targets; non-unital maps and zero rings included |
| Folkman–BANANA countable categorical limit | [Fraïssé class](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanFirstOrderFraisse.lean); [Existence and categoricity](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanFirstOrderExistence.lean#L24); [Mixed-sort tuple orbits](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanFirstOrderTaggedLimitOrbits.lean#L15) | Product encoding with native embedding/substructure correspondence and native decoding of the limit |
| BANANA strong amalgamation, finite age and homogeneity | [Native strong amalgam](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaNativeStrongAmalgamation.lean#L136); [Finite age](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitFiniteAge.lean); [Homogeneity](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitGlobalHomogeneity.lean) | Arbitrary finite bilinear pairings and explicit countable pairing |
| BANANA countable categoricity | [Tagged relational limit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitFirstOrder.lean#L138); [Native tuple orbits](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitMixedTupleOrbits.lean) | Tagged first-order representation and native mixed-sort tuples |

The Folkman finite-class theorem is assembled as a Lean record whose fields are proved. It is not a hypothesis or an external certificate.

## EPPA, amenability and ample generics

| Manuscript result | Main Lean source |
| --- | --- |
| Boolean–BANANA fails EPPA | [Native finite class obstruction](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/PrebananaAbstractClassEPPA.lean#L63) |
| Boolean–BANANA nonamenability | [Stone-space contradiction](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaStoneNonamenability.lean#L100) |
| Folkman–BANANA fails EPPA | [Native finite class obstruction](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanNativeEPPAObstruction.lean#L42) |
| Folkman–BANANA nonamenability | [Native pointwise automorphism group](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanFirstOrderLimitNonamenability.lean#L34) |
| BANANA coherent EPPA | [Native coherent witness](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaNativeCoherentEppa.lean#L161) |
| BANANA amenability | [Dense increasing sequence of finite subgroups](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitTopologicalAmenability.lean#L165); [Invariant probability](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitTopologicalAmenability.lean#L196) |
| BANANA ample generics | [Finite-system JEP and WAP](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaFiniteSystemsJepWap.lean#L167); [Comeagre diagonal conjugacy orbits](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitGenericBackAndForth.lean#L285) |

For coherent EPPA, the native theorem quantifies over arbitrary finite-dimensional left and right carriers and their bilinear pairing. It constructs a single perfect witness with both side dimensions equal to the sum of the input dimensions, and one choice of extensions for every actual partial isomorphism. Identity and composition coherence are explicit equations in the statement.

## Infinite Ramsey degrees and precompactness

| Result | Main Lean source |
| --- | --- |
| Bound on copy degree by pointed generated expansion types | [First-order theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FirstOrderGeneratedRamseyExpansion.lean#L112); [Native finite pointed-cover theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/NativePointedRamseyExpansion.lean#L72) |
| Boolean–BANANA persistent colouring | [Native copy-range colouring](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCopyTransport.lean#L274) |
| Folkman–BANANA persistent colouring | [Native copy-range colouring](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FolkmanRamseyExpansionObstruction.lean#L114) |
| Bilinear residue-surjectivity | [Odd residue-fibre cardinalities](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BilinearResidue.lean#L533) |
| BANANA persistent colourings of the two line-pair sources | [Persistent colouring](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/CopyRamseyDegree.lean#L162); [Sharper pairing-one colouring](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/CopyRamseyDegree.lean#L236); [Infinite copy degrees](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/CopyRamseyDegree.lean#L328) |
| BANANA exact copy Ramsey degrees | [Classification](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaOneSidedCopyDegree.lean#L157) |
| General embedding/copy-degree multiplier | [First-order degree formula](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FirstOrderEmbeddingCopyDegree.lean#L108) |
| BANANA exact embedding Ramsey degrees | [Unconditional classification](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/RamseyDegreeClassifications.lean#L15) |
| Three generated-expansion obstructions | [First-order obstructions](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaGeneratedRamseyObstructions.lean#L21); [Native obstructions](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/NativePointedRamseyExpansion.lean#L119) |

For BANANA, the copy degree is one if at least one sort has dimension zero, and infinite otherwise. In the finite case the embedding degree is the order of the source automorphism group. The formal embedding-degree statement is unconditional on any additional copy-degree hypothesis.

The first-order expansion theorem counts generated expanded domains with the original copy distinguished. The Boolean case uses its marked first-order language. The Folkman product and BANANA functional tagged representations have direct first-order obstruction theorems. The native interface additionally proves all three obstructions on the actual reduct copy systems. Its application to arbitrary many-sorted expansion syntax is the English correspondence explained in [Mathematical representations](Mathematical-representations.md).

## Dynamical and model-theoretic consequences

| Result | Main Lean source |
| --- | --- |
| Co-precompactness and finite splitting of tuple orbits | [First-order pointwise criterion](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/FirstOrderOrbitCoPrecompact.lean#L43) |
| BANANA has no co-precompact extremely amenable subgroup | [Native group theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitExtremelyAmenableDegree.lean#L203) |
| BANANA nonmetrisable universal minimal flow | [Existence and nonmetrisability](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitUniversalMinimalFlow.lean#L42) |
| No countably categorical tagged BANANA expansion has extremely amenable automorphism group | [Expansion group obstruction](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitExpansionGroup.lean) |
| BANANA DEERP | [Tagged complete theory](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitDefinableColouring.lean#L190); [Sorted complete-theory statement](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaSortedDefinableTupleRamsey.lean#L169) |
| Invariant enumeration types and Ellis maps | [Invariant enumeration types](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitInvariantTypes.lean); [Enumeration Ellis maps](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BananaLimitEnumerationEllis.lean) |

The dependency audit explains the hypotheses of the general canonical-amalgamation and invariant-type/Ellis-map implications, including the relevant finite-parameter realisation and homogeneity conditions. The direct native BANANA nonmetrisability proof does not require importing the general reverse implication in Ben Yaacov–Melleray–Tsankov's Theorem 1.1.

## Alternating spaces and the Boolean dynamical application

| Result | Main Lean source |
| --- | --- |
| Countable symplectic model, finite age and homogeneity | [Countable orthogonal sum](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/SymplecticCountableModel.lean); [Actual alternating-space amalgamation](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/SymplecticCopySystem.lean#L140) |
| Quadratic residue theorem | [Odd residue-fibre cardinalities](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/QuadraticResidueStandard.lean#L40) |
| Infinite degree of a line and classification of copy degrees | [Copy-degree classification](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/SymplecticCopyDegree.lean#L178) |
| Alternating-space embedding degrees | [Embedding-degree classification](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/RamseyDegreeClassifications.lean#L28) |
| Boolean–BANANA compact metrisable minimal charge flow with all orbits meagre | [Dense and meagre orbits](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderPadicCharge.lean#L87); [Minimal charge flow](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderPadicCharge.lean#L96); [Failure of the generic point property](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderPadicCharge.lean#L107) |
| Positive-mass realisations on the fixed marked limit | [Existence for every allowed odd-prime set](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderMassSubgroups.lean#L21) |
| Closed maximal amenable mass subgroups, not extremely amenable or co-precompact | [Subgroup properties](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderMassSubgroups.lean#L41) |
| Exactly continuum many conjugacy classes of closed maximal amenable subgroups | [Cardinality theorem](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/BANANA/NonPrecompact/BooleanBananaCylinderMassSubgroups.lean#L31) |

The symplectic age includes degenerate alternating spaces, in particular lines. Both Ramsey degrees are one for the zero space and infinite for every positive-dimensional space. The Boolean mass-subgroup property theorem takes a realisation as an argument; its existence is proved separately and the continuum cardinality theorem is unconditional.

For more auxiliary lemmas and exact declaration names, see the [pinned repository proof map](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/README.md#proof-coverage).
