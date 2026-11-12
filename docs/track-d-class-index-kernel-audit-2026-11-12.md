# Track D — kernel-checked class-index descent (12 November 2026)

**Internal audit note.** The circulation manuscript is frozen and untouched. This is verification of a generic groupoid lemma, not yet of the complete BANANA coherent-EPPA theorem.

## Pinned local environment

- Lean 4.35.0-rc3, Lake 5.0.0-src+470d5ce, Mathlib pinned at 5bd58ac291422a21f412ae354c91e7d172255a2c.
- Recovered existing compiler/Mathlib bundles from gluing-EPPA run 42512209025; all nine ZIP CRCs, split archive SHA-256 checks, and both whole-archive SHA-256 checks passed. No new GitHub Actions were run.
- Built in a separate temporary mathlib-only Lake workspace using exact pinned Mathlib cached oleans, not the full BANANA project checkout.

## Exact new source and real Lean build

Source: BANANA/NonPrecompact/CoherentGroupoidDescent.lean
Git blob: 58fabd32a50f21aa813f700d21475ba2a58b990f

Audit: BANANA/NonPrecompact/CoherentGroupoidDescentAxiomAudit.lean
Git blob: bdcfc5ad3283b82c49e04a84359792d449006642

Both blobs match the source files used for a genuine successful local build:

    LEAN_NUM_THREADS=1 lake build +BANANA.NonPrecompact.CoherentGroupoidDescentAxiomAudit

**Result:** Build completed successfully (325 jobs). Running the same axiom-audit file through lake env lean also succeeded.

| Theorem | Transitive axioms |
| --- | --- |
| classAction_changeIndex | None |
| classAction_descend_refl | propext |
| classAction_descend_trans | None |
| classAction_descend_symm | propext |
| classAction_descend_extends | None |

There are no sorry, admit or newly declared axioms.

An independent abstract type-elaboration adapter was compiled using the same implicit class-object binder shape employed by the staged BANANA source. Identity, composition and inverse adapters all passed. The adapter audit printed only propext for identity/inverse and no axioms for composition. This test did NOT import the actual BANANA matrix structures.

## Integration into draft PR #310

- Added the generic, now kernel-checked class-index descent and its axiom audit.
- BananaActualSubpairUnindexedCoherence.lean imports that module, uses its fixed-source-class action, and delegates the identity, composition and inverse proof steps to the checked lemmas. This removes duplicate dependent transport reasoning.
- The exact-head local verification driver now includes ten Track D audit modules; its mock verifier expects ten entries.

**Verification boundary:** The modified BANANA-specific unindexed theorem and all matrix/class-family dependencies have NOT yet been compiled. The full exact-head source checkout and pinned successor-tree dependency chain still need restoration. Independent adversarial referee review has not occurred. Leave the PR draft/unmerged; do not add a circulation validation marker.

Next: build the remaining BANANA-specific modules in dependency order and inspect every axiom report. Do not use GitHub Actions.
