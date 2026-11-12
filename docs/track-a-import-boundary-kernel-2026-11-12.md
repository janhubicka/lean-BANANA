# Track A: local imported-module kernel validation — 12 November 2026

Internal validation record only. The BANANA circulation manuscript remains frozen.

## Provenance
- PR #312 branch: `audit/track-a-shared-edgecount-cast-20261106`, source inspected from head `fe3239112c5969fe6bbcd565cc40752ec3757045` (no new mathematical source changes in this test).
- Toolchain: Lean `v4.35.0-rc3` (commit `470d5ce`), Lake `5.0.0-src+470d5ce`.
- Mathlib: `5bd58ac291422a21f412ae354c91e7d172255a2c`.
- All toolchain and mathlib packages were restored **locally** from existing checksum-verified offline artefacts of lean-gluing-eppa run #42512209025. No new GitHub Actions runs were started.

## Exact source-fidelity comparison
Extracted and normalised whitespace/comments independently in the local kernel reproduction and the GitHub PR source. The 13 composition declarations, six shared counting declarations and lemmas, and the original `FolkmanAtomStructure` and `FolkmanAtomEmbedding` signatures matched in length and FNV-1a digest. (FNV-1a is a source-matching check, not a cryptographic provenance signature.) No theorem statement was changed. The two native/tuple wrapper statements had already been checked to match their mainline declarations.

## Actual local Lean checks
1. Reran `TrackAIsolatedNarrow.lean` using the restored compiler: exit 0, **20/20** `#print axioms` reports; only `propext`, `Classical.choice`, `Quot.sound`, or no axioms.
2. Reconstructed `BANANA.NonPrecompact.FolkmanPersistence` as a *narrow-import local stub* with the exact mathematical definitions and prerequisite lemmas, then compiled it to `.olean`.
3. Compiled the Track A composition definitions/proofs as a separate `BANANA.NonPrecompact.FolkmanPartialOwnerComposition` module importing the local stub; exit 0. Compiled a third module importing this `.olean` and printing axioms for all 13 composition declarations; **13/13** reports matched, all permitted.
4. Compiled `folkmanTuple_edgeCount_cast` and `folkmanNativeFin_edgeCount_cast` as two distinct imported modules, both delegating to the generic shared lemma; exit 0. In a separate imported audit all four sampled composition/wrapper declarations produced permitted-axiom reports.

A reproducible ZIP of these lean sources, the audit files and the log files was generated as `banana_track_a_imported_kernel_20261112.zip` (SHA-256 `46804775221334b810cec41c782502c4f39dcf1ca5286fd7cd9da5c5099a3309`). It is a standalone verification artefact, **not** a full BANANA checkout.

## Remaining non-negotiable gate
**Do not merge PR #312 or mark manuscript proofs validated based on these tests alone.** The restored offline workspace contains matching Lean and mathlib, but not the complete, exact-head source checkouts of:
- `janhubicka/lean-BANANA` at PR #312 head;
- `janhubicka/lean-successors` at `d9be105f73ca5a0f3f411b87d4c2419d0eb94753`;
- `janhubicka/lean-ramsey-space-todorcevic` at `54a9eb02f7f7bd2e942e95f7b44fc6f04f48892c`.

The exact-head `bash scripts/check_track_a_local.sh` (full build and transitive-axiom audit) has **not** run, and no independent adversarial model-referee sign-off has been obtained. A successful isolated/imported `.olean` check does not verify the rest of the repository import graph or original-language representation bridge. The circulation TeX remains untouched.
