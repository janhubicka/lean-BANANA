# Track A independent Lean-kernel reproduction — 11 November 2026

Internal validation note. **Do not change or mark the frozen circulation paper.**

## Provenance and scope

PR #312's new composition declarations were independently reproduced in a
stand-alone Lean file using the same mathematical signatures as
`FolkmanPersistence.lean` for `F2 = ZMod 2`, `folkmanEdgeCount`,
`folkmanFiber`, `FolkmanAtomStructure`, and `FolkmanAtomEmbedding`.
The proof bodies of the 13 declarations in
`FolkmanPartialOwnerComposition.lean` were copied into the reproduction.
Necessary finite-sum lemmas and the binary-element classification were
copied from the existing BANANA sources. The independent local workspace
used only narrow mathlib imports:

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
```

The environment was recovered from pre-existing, checksum-verified
Ubuntu artefacts of lean-gluing-eppa run #42512209025. **No new GitHub
Actions job was started.**

- Lean: `leanprover/lean4:v4.35.0-rc3` (commit `470d5ce`)
- Lake: `5.0.0-src+470d5ce`
- Mathlib: `5bd58ac291422a21f412ae354c91e7d172255a2c` (matching BANANA's
  pinned lean-successors revision `d9be105f73ca5a0f3f411b87d4c2419d0eb94753`)
- Command: `LEAN_NUM_THREADS=1 lake env lean TrackAIsolatedNarrow.lean`

## One actual elaboration failure and repair

The initial isolated compilation rejected the final step in the `some j`
case of `folkmanFiber_compose`: after simplification the goal was
`some j = some j`, but the proof used `exact hg`, whose type was
`g x = some j`. Replacing that single proof line by `rfl` repaired the
failure. This was committed directly to PR #312 in
`8f6a31fd9c6c99cec53674cd333ce22ba7e58f1d`; the declaration and
all hypotheses are unchanged.

The first narrow-import run also lacked `Nat.cast_sum`; adding the
standard `Mathlib.Algebra.BigOperators.Ring.Finset` import fixed this
*reproduction-only* missing-import error. In the actual repository the
upstream `FiniteOwnerSums` already imports `Mathlib`, so no
repository import changes were needed.

## Kernel results

On the repaired, narrow-import reproduction the command exited with
status 0. The full 13-declaration set compiled, and every active
`#print axioms` returned only allowed axioms:

- `folkmanComposeOwner` and `folkmanIdentityOwner`: no axioms.
- Remaining definitions/theorems: subsets of `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `sorryAx` or custom axioms were reported.
- A further isolated run checked five shared prerequisites as well: `f2_eq_zero_or_one`, `folkmanEdgeCount_cast`, `folkmanFiber_pairwiseDisjoint`, and both `folkmanEdgeCount_biUnion_*` identities. All 18 reports contained only the same three allowed axioms (or none), with status 0. The extended run took 4.44 seconds.

These statements cover exact `Option.none` propagation, composite fibre
unions, non-empty source fibres, pairing-preserving atom-coordinate
composition, identity, associativity, and equality of embedding records
from their owner maps. The test also includes zero-dimensional sorts
because no non-emptiness assumption is inserted.

## Strict limitation / remaining gate

**This is real kernel validation of a stand-alone reproduction, NOT an
exact-head build of the actual BANANA repository.** The destination
container still lacks the source checkouts of BANANA, lean-successors and
lean-ramsey-space-todorcevic at their pinned SHAs. Compiling copied
definitions does not check import-qualified names, possible namespace
conflicts or the complete downstream integration. Nor is the local
source-level mathematical review an independent external referee.

PR #312 must remain DRAFT and unmerged. Once an exact-head checkout of
all three projects is available locally, run:

```sh
bash scripts/check_track_a_local.sh
```

Then perform independent adversarial statement-fidelity and
counterexample reviews against the original native non-unital embedding
interface. Do not promote manuscript verification markers until those
checks succeed.
