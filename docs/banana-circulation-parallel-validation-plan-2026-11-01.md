# BANANA circulation validation: adversarial audit and parallel work plan

## Verification update — 6 November 2026

This document's original 1 November status paragraphs are a historical snapshot.
The current BANANA manuscript PR #241 has been merged, and its circulation prose
remains frozen; only TODOs and validation markers may be added without approval.
The Folkman tuple-profile PR #306 passed a full, exact-head historical Lean build
and was merged on 6 November as lean-BANANA commit fe4f219ed52b3b041d1a7d02e62ae4b6cb146f6c.
The earlier PR #305, and its dependent Track B PR #309, have recorded Lean
build failures. PRs #308, #310 and #311 require their own kernel verification.

The total-owner proof refactor in this PR #307 passed a full exact-head Lean
build and a separate \`#print axioms\` audit on 1 November at commit
0dfa4e18014321a46b3d7d85bb26b7f1cbf3a9b9; it uses only propext,
Classical.choice and Quot.sound. The axiom-report parser has subsequently
been strengthened to check declaration names, not only report counts; those
Python-only changes have targeted independent regression tests, but no new
Lean build was started. The mathematical source and theorem signature are
unchanged since the successful run.

1 November 2026. Internal development note only; NOT circulation prose.

## Fixed references and change permissions

Lean main inspected: 7bbfc5846a0223c9028aa50dc442aef88ce3f01a (30 October 2026).
Manuscript main inspected: 02403a13ff8d318e3e50f62114f6aa5155efa632 (30 October 2026).
Lean PRs 305 and 306 are draft and not kernel-checked, despite being conflict-free.
Manuscript PR 241 is draft and contains the known Folkman-status and symplectic-correction TODOs. Avoid duplicating previously rejected or removed notes.

Circulation prose, mathematical statements, equations, references and figures remain frozen. Only TODO notes and validation markers are permitted without explicit author approval. The appendix is excluded. Compile all TeX locally and inspect PDFs and latexdiffs. GitHub runners are out of budget, including for Lean, so the exact PR heads require locally run Lean builds.

## Adversarial findings

1. pre-BANANA. The finite marked Boolean class, explicit countable cylinder limit, exact finite age, extension property, marked ultrahomogeneity and genuine finite tuple orbit bounds have kernel-checked constituents through merged PR 270. Ryll–Nardzewski is an external standard implication. Conditional mass identities do not by themselves construct a continuous Stone action or prove automorphism-group non-amenability.
2. Folkman–BANANA. Native non-unital strong amalgamation, pairing preservation, intersection and finite-class ingredients have substantial merged proofs through PR 302. Draft PR 305 provides finite atom indexation and native morphism/pairing transport, but its Lean elaboration and axiom audit have not run. Draft PR 306 provides finite non-unital tuple profiles and embedding invariance, not profile completeness or actual countable-limit orbits. The zero ring and Option.none private target atoms must be tested explicitly.
3. BANANA. The finite pairing-model and coherent-extension ingredients, explicit countable model and finite-GL density arguments must be distinguished from the class-wide coherent EPPA representative bookkeeping and topological amenability/ample-generics conclusions. A constituent lemma cannot stand in for the complete conclusion without verifying its hypotheses.
4. Copy Ramsey degrees. Check unlabelled copies rather than embeddings, the ambient colouring before the target embedding, the degenerate and one-sided cases, and the exact external successor-tree theorem. Persistent colourings and the no-precompact-expansion implication are separate arguments.
5. Symplectic application. Existing issue 240 and manuscript PR 241 describe four problems: the printed class of nondegenerate finite symplectic spaces is not hereditary and excludes one-dimensional structures; the quadratic residue Q_C modulo 2 has polar form beta, rather than being beta; the high-moment unweighted divisibility assertion is false; and the cited two-sorted BANANA amalgamation theorem is not the one-sorted alternating-space AP. The intended age should include all finite alternating spaces. Do not rewrite these statements until the authors explicitly approve correction.
6. Reuse opportunity already staged here. The finite sum over source fibres with a prescribed base is a specialisation of the generic total-owner finite sum identity in FiniteOwnerSums. PrebananaFibrewiseSum now calls that existing theorem without altering its statement. FolkmanPersistence already uses the generic partial-owner finite sum. This edit is UNVERIFIED pending an exact-head Lean build.
7. Duplicate draft functionality. PR 305's folkmanNativeFin_edgeCount_cast and PR 306's folkmanTuple_edgeCount_cast calculate the same natural-number edge-count cast into F2. When a version is kernel-checked, move it to a common Folkman pairing layer and import it from both variants. PR 305 also repeats a local Fintype AsBoolAlg transport instance in three modules. Extract it only after confirming no unwanted global typeclass instance or new import cycle. No general embedding abstraction should identify total pre-BANANA, partial non-unital Folkman, and linear BANANA embeddings.
8. No newly found dead proof module may be deleted solely because it is missing from the root's direct imports: transitive imports and axiom-audit imports also count. Use the existing graph script and inspect downstream dependencies before removals. Avoid retaining superseded proof branches merely because there is no current proof importer; Git history preserves rejected attempts.

## Independent parallel tracks and file ownership

Track 0 — Shared API and code audit. Owner: FiniteOwnerSums, PrebananaFibrewiseSum, shared Folkman counting, verification scripts and internal notes. Work: simplify finite fibre sums, inventory dead statements, consolidate one incidence-count cast. Exit: no changed theorem signatures, at least two downstream users of any new general lemma, full build and axiom audit.

Track 1 — Folkman finite native class. Owner: FolkmanNativeFinite* and class-data modules. Start with draft PR 305, verify actual ring operations, the four original non-unital maps, pairing preservation, private atoms, zero rings, composition and exact intersections; package native HP, JEP, strong AP and countable isomorphism representations. Exit: an end-to-end original-language finite-class theorem, not merely separate atom-coordinate certificates.

Track 2 — Folkman tuple invariants. Owner: FolkmanTupleProfiles* modules. Start independently with draft PR 306. Prove that the generated non-unital ring is precisely the unions of realised NONZERO pattern fibres; equal profiles must give an isomorphism of generated two-sort structures with its original cross-pairing. Exit: completeness of finite profiles for the finite coordinate class. The final automorphism-orbit theorem waits for the homogeneous countable limit from Track 1.

Track 3 — BANANA coherent EPPA and dynamics. Owner: CoherentEppaPackage, CoherentConjugation, finite perfect blocks and BananaLimitFiniteGL* modules. Audit representative choices, coherent composition, dimension bound, stage inclusions, group-law and density. Separate exact global coherent EPPA from group-topological deductions. Exit: two disjoint certificates: complete coherent extension and the external or formal bridge to group amenability.

Track 4 — Copy Ramsey degree and successor bridge. Owner: BananaCopyDegree*, PrebananaCopyDegree*, and BinarySubspaceRamsey* modules. Audit one-sided/two-sided bounds, copies versus embeddings and entire finite-colouring quantifiers; pin the used successor-tree SHA. Exit: exact theorem-to-manuscript map, with any standard external consequences explicitly identified.

Track 5 — Symplectic proof and corrections. Owner: Symplectic*, Quadratic*, MatrixAffineParity and regression scripts. Independently test the corrected hereditary age of all finite alternating spaces, one-sorted AP, polarisation, Gauss-sum argument and weighted moment divisibilities. Exit: a kernel-checked statement of the corrected result and a precise correction TODO. Manuscript prose remains untouched until authorised.

Track 6 — Stone actions and maximal amenability. Owner: PrebananaAmenability*, PrebananaStoneMeasureMass and isolated new modules. Prove or clearly cite the action and measure interface; separate finite invariant-mass obstructions, orbit transitivity, open subgroup inheritance and maximal amenability. Exit: explicit non-circular theorem chain identifying each topological hypothesis.

Integration — one owner alone edits BANANA.lean, re-pins verification links and proposes TeX TODO/validation markers after checks. Split content ownership prevents parallel branches from competing for root imports and manuscript margins. Merge 0 only after building; Tracks 1–6 can start from a common checked main. Only Track 2's *global-orbit* conclusion depends on Track 1; other initial tasks have no mathematical dependency. Integrate by cherry-picking reviewed branches in order and rebuilding exact heads.

## Three separate referee obligations per result

A. Statement fidelity: compare the exact Lean declaration, all implicit parameters and assumptions, the real embedding notion, and the printed theorem. Classify coverage as exact, stronger, weaker, conditional or representation-level.

B. Counterexample search: adversarially attempt empty rings, unowned target atoms, mixed-sort zeros, degenerate pairings, per-base rather than total marks, non-hereditary symplectic ages, duplicate embeddings of one copy, and reversed colour/embedding quantifiers. Do not substitute random checks for a theorem.

C. Kernel proof: run Lean on the exact commit and inspect ALL transitive axioms. Only propext, Classical.choice and Quot.sound are allowed. An LLM's independent-looking review is NOT an independently spawned referee.

## Exact local gate

1. python3 scripts/check_lean_module_graph.py
2. lake build BANANA
3. bash scripts/audit_all_axioms_local.sh
4. python3 scripts/check_finite_owner_base_sums.py (for this refactor) and targeted regressions for each track.
5. Independently check theorem fidelity and corner cases, recording the precise kernel-checked commit SHA.
6. For any manuscript PR, mechanically strip TODO and validation-marker commands from base and head and assert equality of the remaining circulation source; compile locally, inspect PDF and latexdiff. No GitHub Actions.

A PR with finite regressions but no local Lean build remains DRAFT / UNVERIFIED. This audit has not launched any independent model referee and does not claim a complete kernel recheck.

## Track A implementation update (same day)

- `PrebananaFibrewiseSum_identity` now uses `finiteTotalOwner_sum_fibres`; no theorem header, quantifier, typeclass or conclusion was changed. Its direct umbrella `Mathlib` import was dropped because the shared module already imports it. This Lean refactor has **not** yet passed an exact-head kernel build.
- `scripts/check_finite_owner_base_sums.py` passed 131,022 base-specific total-owner and 31,678 partial-owner finite configurations when run locally. It now also exhibits a noncommuting-base counterexample: the unrestricted global sum remains the same, while the separate base-fibre totals differ. This confirms that the commuting hypothesis is essential.
- The local axiom-audit runner now checks one result **per active** `#print axioms`, rather than accepting one output for an entire audit file. Unexpected transitive axioms, `sorryAx`, missing and extra results all fail. The parser ignores line and nested block comments.
- The import-graph checker shares this comment parser, verifies that axiom audit declarations are active, and distinguishes root-reachable production modules from **audit-only** proof modules and genuinely unreachable files. Audit-only does not justify deletion.
- `python3 -m unittest discover -s scripts -p 'test_*.py'` passed 9 local fixture tests (8 axiom-output checks and 1 synthetic import-graph test). `bash -n` also accepted the revised audit shell script. These are Python/shell checks, not a Lean build.
- Selective GitHub source inspection found long transitive chains such as `BananaOneSidedCopyDegree -> BananaOneSidedCopyRanges -> BananaCopyDegree -> BananaCopyPalette -> BananaCopyRanges -> BananaEmbeddingDegree -> LinePairExtension` and `BananaTriplePairing -> BananaTripleIntersection -> BananaTripleStrongImages -> BananaTripleCoordinates`. Thus deletion by checking only direct imports is unsafe. The **full** repository import graph must be run locally before removing any candidate.
- Two separate `folkmanEdgeCount` integer-to-F2 conversion lemmas are still present only in unverified Folkman draft PRs #305 and #306. Consolidate them once those branches are locally checked, retaining the class-specific code elsewhere.

All Track A changes are in the **Lean repository only**. Neither the frozen circulation manuscript nor its appendix was modified.
