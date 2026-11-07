# Track C — native generated-ring bridge and adversarial review, 3 November 2026

**Status: source drafted; not Lean kernel-verified.** No manuscript or
appendix files were touched. Do not merge or insert green markers.

## Correction to earlier API review

The previous review comment treating `≃+*` as inherently unital was
**incorrect**. The project's pinned Mathlib
(`5bd58ac291422a21f412ae354c91e7d172255a2c`),
`Mathlib/Algebra/Ring/Equiv.lean`, describes `RingEquiv` as an
equivalence of non-unital (even non-associative) semirings and declares
it using additive/multiplicative equivalences rather than preservation
of one. `NonUnitalSubring` inherits the required non-unital ring
structure. Keep `≃+*`; do **not** replace native non-unital closure by
a unital subring. The correction is posted on PR #308.

The previous concern about `rfl` in the inverse proofs was also too
strong: by the definition of `folkmanGeneratedRingTermMap`, the chosen
source term evaluates definitionally to the value of the map. The
`rfl` supplied to the term-map evaluation theorem is therefore
plausible. **Lean has not confirmed elaboration.**

## Concrete repair

The prior `map_add'` and `map_mul'` blocks relied only on evaluation
of the *combined* ring term. This does not directly establish
preservation of addition/multiplication: the right-hand side refers
to the images of each operand, represented by independently chosen
terms. They now separately derive
`map(x) = eval_B(representative(x))` and
`map(y) = eval_B(representative(y))` before using the term constructors.
The repair is in commit `7ca7a80638792d9abd4a69ae1cc459395f47b1d9`.
This is a real proof-term gap repair, still unverified by Lean.

## New native-carrier transport

`FolkmanNativeRingTermCoordinates.lean` reuses the existing generic
`FolkmanRingTerm.eval_map`, together with the already available
`folkmanNativeRingAtomEquiv_zero/add/mul`, to show that evaluating
any non-unital ring term commutes with the original finite Boolean
ring's canonical atom-coordinate equivalence. Consequently native
ring-term equation kernels and their atom-code counterparts coincide.
This holds for the one-element zero ring and requires no preservation
of the ambient unit by embeddings.

`FolkmanGeneratedTwoSortProfileIso.lean` packages the complete finite
classification interface: two native non-unital generated-ring
equivalences, preservation of every distinguished generator and of
the F2 cross-sort pairing on *all* generated elements. Its hypotheses
are equality of the complete two-sort tuple profiles. It does not
assert equivalence of the entire ambient models or an automorphism
of a homogeneous limit.

Both new modules have dedicated `#print axioms` files imported through
the existing Track C audit chain, hence transitively through
`BANANA.lean`. These declarations still require exact-head build and
axiom inspection.

## Executed semantic checks (not Lean)

The local normalisation regression was rerun: 278 Boolean truth tables,
131,624 binary-constructor checks, 5,000 seeded term checks, 689
generated closure/isomorphism cases, 39,400 operation checks and 1,940
generator checks. A separate small native-code/representative
regression passed 52,860 atom-code evaluations, 1,200 equal-pattern
ambient pairs, 12,084 independently chosen term representatives,
144,000 operation-preservation assertions and 1,800 named-generator
checks. The exact new regression is committed as
`scripts/check_folkman_native_term_coordinate_bridge.py`.

These regressions inspect finite semantic models, **not Lean code**.
No other independent referee agent was available or spawned. The
mathematical/source review remains a single-assistant audit, not
independent certification.

## Local verification boundary

The current container has neither `lean`, `lake` nor `elan`,
and DNS access to GitHub fails. No full checkout, kernel elaboration,
axiom audit or LaTeX build was performed. No GitHub Actions jobs were
dispatched (runners are out of budget). Only changed-file import
existence checks and GitHub tree/commit comparisons can be carried
out via the connected repository API.

### Merge gate

On exact PR head, run locally:

```sh
python3 scripts/check_lean_module_graph.py
lake build BANANA
bash scripts/audit_all_axioms_local.sh
python3 scripts/check_folkman_tuple_term_completeness_small.py
python3 scripts/check_folkman_nonunital_normalisation.py
python3 scripts/check_folkman_native_term_coordinate_bridge.py
```

Then obtain independent adversarial reviews for the exact Lean theorem
statements and the finite ambient/native comparison. Draft PR #306,
the parent, is also unverified and must pass its own kernel build.

## Next mathematical task

Bridge the paired finite ring-isomorphism interface to the *original*
two-sorted native pairing on arbitrary finite Boolean-ring carriers,
using the existing atom-coordinate pairing-transport theorem and
Track B's finite `Fin`-index packaging. Only after a homogeneous
countable Folkman limit is constructed and its finite-generated
isomorphisms are shown to extend to automorphisms may finite
tuple profiles be used to deduce oligomorphic orbit bounds and
`\\omega`-categoricity (with Ryll–Nardzewski external if desired).
