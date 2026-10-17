# lean-BANANA

Lean 4 formalisation supporting the **BANANA** manuscript. The circulation
manuscript is maintained separately in [janhubicka/BANANA](https://github.com/janhubicka/BANANA).
Its circulation text is frozen: mathematical corrections should be proposed
as TODOs, not silently applied.

The library is organised around three related, but **different**, classes.
In particular, unital Boolean-algebra embeddings in pre-BANANA must not be
confused with non-unital Boolean-ring embeddings in Folkman–BANANA.

## Source map and proof status

The following is a guide to the proof statements, not a claim that every
consequence in the paper is already a theorem of Lean.

| Development | Established in the Lean sources | Further obligations |
| --- | --- | --- |
| **pre-BANANA** | Finite marked Boolean-algebra models, strong amalgamation, heredity, joint embedding, EPPA obstruction and persistent copy colourings; the unconditional finite-extension theorem for arbitrary marked Boolean embeddings; explicit five-ary tower and finite-model universality; a countable Boolean algebra of cylinders with well-defined, disjoint-additive F₂ marking; compatibility with all finite-stage embeddings; simultaneous finite-stage presentations for finite families | Factor arbitrary finite marked embeddings into a finite stage, obtain the extension property and ultrahomogeneity of the countable algebra, prove finite tuple-orbit bounds, and handle Stone/topological consequences separately. Conditional measure-obstruction hypotheses remain explicit |
| **Folkman–BANANA** | Non-unital atom-owner representation; individual Boolean-ring-sort amalgamation and exact image intersection; bilinear block-extension calculations; persistent copy colourings and infinite copy Ramsey degree | Combined two-sorted, pairing-preserving strong amalgamation and finite-age/limit conclusions need the remaining integration work |
| **BANANA** | Bilinear-pairing matrix models, perfect completion and finite amalgamation; explicit countable pairing, finite age, finite-substructure homogeneity and finite tuple-orbit criteria; locally finite finite-GL approximation; algebraic constituents of coherent EPPA; persistent colourings and copy Ramsey degrees | Final group-theoretic deductions (including topological amenability and ample generics) and the finite representative bookkeeping for a fully packaged coherent-EPPA assertion are not all expressed as end-to-end Lean theorems |

Some theorems are stated in standard finite coordinates or as conditional
interfaces. Their hypotheses must be checked when using them to justify a
manuscript proposition. In particular, a theorem about an invariant
probability mass is not itself an existence theorem for a Stone action.

The principal files are under `BANANA/NonPrecompact/`:
`PrebananaFiniteBooleanModelStrongAP.lean`,
`PrebananaCopyDegree.lean`,
`PrebananaExplicitFiveAryTower.lean`,
`PrebananaFiveAryCylinderMarkedModel.lean`,
`PrebananaFiveAryCylinderFiniteFamily.lean`,
`FolkmanAtomAmalgam.lean`,
`FolkmanPersistence.lean`,
`BananaStructure.lean`,
`BananaLimitGlobalHomogeneity.lean`,
`BananaLimitLocallyFiniteDense.lean`,
`CoherentEppaPackage.lean`, and
`BananaCopyDegree.lean`.

For the five-ary extension proof, start with
`docs/prebanana-five-ary-fraisse-construction.md`. The finite-parent-fibre allocation theorem was verified and merged
via [PR #223](https://github.com/janhubicka/lean-BANANA/pull/223).
The full common-base-commuting finite extension **in marked powerset
coordinates** was checked and merged in [PR #231](https://github.com/janhubicka/lean-BANANA/pull/231);
[PR #232](https://github.com/janhubicka/lean-BANANA/pull/232)
identifies its prefix map with the actual iterated tower embedding, and
[PR #235](https://github.com/janhubicka/lean-BANANA/pull/235)
packages arbitrary finite Boolean algebras as marked atom powersets.
The original-embedding atom-partition bridge
([PR #234](https://github.com/janhubicka/lean-BANANA/pull/234)
and [PR #237](https://github.com/janhubicka/lean-BANANA/pull/237))
is also verified and merged. The integration lemma
([PR #236](https://github.com/janhubicka/lean-BANANA/pull/236))
and **unconditional** arbitrary-carrier finite-extension theorem
([PR #238](https://github.com/janhubicka/lean-BANANA/pull/238))
are now verified and merged.
The concrete **countable cylinder carrier** with faithful finite-stage
injections ([PR #239](https://github.com/janhubicka/lean-BANANA/pull/239))
and its compatibility with tower iteration
([PR #240](https://github.com/janhubicka/lean-BANANA/pull/240))
are also verified. Finite-model universality
([PR #245](https://github.com/janhubicka/lean-BANANA/pull/245)),
stage-independent marking
([PR #242](https://github.com/janhubicka/lean-BANANA/pull/242)),
Boolean closure
([PR #243](https://github.com/janhubicka/lean-BANANA/pull/243))
and the admissible countable marked cylinder algebra
([PR #244](https://github.com/janhubicka/lean-BANANA/pull/244))
are kernel-checked and merged. Simultaneous finite-stage presentations
for finite families are verified in
[PR #247](https://github.com/janhubicka/lean-BANANA/pull/247).
Finite embedding factorisation
([draft PR #248](https://github.com/janhubicka/lean-BANANA/pull/248)),
the packaged finite-to-countable marked embedding interface
([draft PR #250](https://github.com/janhubicka/lean-BANANA/pull/250))
and countable extension transfer
([draft PR #251](https://github.com/janhubicka/lean-BANANA/pull/251))
remain under verification. Exact finite age, ultrahomogeneity and
topological deductions are **not yet** end-to-end Lean theorems.

## Local verification

Use the toolchain in `lean-toolchain` and the dependencies pinned by
`lakefile.toml`. From a checkout with Lean/Lake installed:

```sh
lake build BANANA
bash scripts/audit_all_axioms_local.sh
```

The first command compiles the library. The second runs
`scripts/check_lean_module_graph.py`, compiles every
`*AxiomAudit.lean` entry point, and checks each printed transitive
axiom set against **exactly** `propext`, `Classical.choice`, and
`Quot.sound`. Unexpected axioms (including `sorryAx`) make the audit
fail. This proves neither theorem-statement fidelity nor the
remaining conditional hypotheses in the manuscript.

Run `python3 scripts/check_lean_module_graph.py` separately to report
unreachable source modules, missing local imports, import cycles,
and empty axiom-audit entry points without invoking Lean.

There are small independent finite regression scripts in `scripts/`;
these supplement, but do not replace, Lean kernel checks. For the
current adversarial findings, scope restrictions and maintenance
decisions see
`docs/formalisation-adversarial-audit-2026-10-15.md`.

## Reusable tools

The existing development already shares the `F2` residue palette,
subset-sum arguments and copy-colouring definitions. The Folkman
bilinear extension also reuses the BANANA zero-cross-block matrix
amalgamation rather than maintaining a second matrix construction.

A worthwhile further extraction is a **finite-fibre calculus** for
disjoint blocks, inverse-image maps, sum decomposition and preservation
of prescribed markings. It should accommodate both total surjective
owner maps (pre-BANANA) and partial `Option`-valued owner maps
(Folkman–BANANA). The `Option.none` fibres are essential and cannot
be erased by declaring the two classes' embeddings equivalent.
Matrix pairing preservation is a further condition, not a consequence
of marked finite-set allocation.

Keep the small, concrete instances in use until a common lemma has at
least two genuine downstream applications. Historical attempts can be
recovered from Git rather than retained as unused parallel APIs.
