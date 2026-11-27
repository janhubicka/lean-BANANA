# Using the Lean companion

## Reproduce the verified development

Use the exact snapshot linked from the [verification page](Verification-and-proof-boundaries.md):

```sh
git clone https://github.com/janhubicka/lean-BANANA.git
cd lean-BANANA
git checkout fc0972fda0cc25ab94ab7315f6f57b7eed9127b9
lake exe cache get
bash scripts/verify_release_candidate.sh
```

Install Lean through elan and use the toolchain specified in `lean-toolchain` (Lean 4.35.0-rc3). The committed `lake-manifest.json` pins the entire dependency graph. Do not run `lake update` for the release reproduction. The cache download is optional; without it the build may require compiling dependencies.

| Principal dependency | Pin |
| --- | --- |
| lean-successors | [d9be105](https://github.com/janhubicka/lean-successors/tree/d9be105f73ca5a0f3f411b87d4c2419d0eb94753) |
| lean-ramsey-space-todorcevic | [54a9eb0](https://github.com/janhubicka/lean-ramsey-space-todorcevic/tree/54a9eb02f7f7bd2e942e95f7b44fc6f04f48892c) |
| mathlib | [5bd58ac](https://github.com/leanprover-community/mathlib4/tree/5bd58ac291422a21f412ae354c91e7d172255a2c) |

The [manifest](https://github.com/janhubicka/lean-BANANA/blob/fc0972fda0cc25ab94ab7315f6f57b7eed9127b9/lake-manifest.json) records all other dependencies. The release script requires a clean checkout, builds the root and audit modules, checks every transitive-axiom report and the direct project/manuscript declaration inventories, performs fresh kernel replay, runs the Python tests and verifies that the dependency files remain unchanged. Logs are stored under `.lake/banana-release-audit/<SHA>/`.

## Main imports and declarations

The public root is `import BANANA`. More focused imports are available under `BANANA.NonPrecompact`. The following names identify checked endpoints in the pinned revision:

```lean
import BANANA

open SuccessorTree.NonPrecompact

#check BooleanBanana.strongAmalgamation
#check folkmanNativeCompleteFiniteClass_nonempty
#check exists_folkmanFirstOrderLimit_categorical
#check BananaNative.exists_coherentEppaWitness
#check BananaMatrixStructure.copyRamseyDegree_classification
#check bananaEmbeddingRamseyDegree_classification
#check FiniteAlternatingSpace.embeddingRamseyDegree_classification
#check booleanBanana_noFinitePointedCover
#check folkmanNative_noFinitePointedCover
#check banana_noFinitePointedCover
#check bananaLimit_exists_comeagre_diagonalConjugacyOrbit
#check bananaLimit_exists_nonmetrizable_universalMinimalFlow
#check bananaTagged_completeTheory_hasSortedDefinableTupleRamsey
#check BooleanBanana.mk_cylinderClosedMaximalAmenableConjugacyClass
```

Use `#print axioms` on any declaration to inspect its transitive axiom dependencies. Inspect the full type before using a conditional theorem. The [statement crosswalk](Formalised-statements.md) gives source locations and the [repository proof map](https://github.com/janhubicka/lean-BANANA/blob/fc0972fda0cc25ab94ab7315f6f57b7eed9127b9/README.md#proof-coverage) lists additional lemmas.

A full ordinary build can also be run with `lake build BANANA`. For release-level checks prefer the strict script above.
